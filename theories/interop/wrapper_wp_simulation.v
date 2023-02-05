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
From melocoton.interop Require Import linking_wp basics wrapper_wp wrapper_wp_block_sim.
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
  1: destruct Hpriv as (mem_r & ->%repr_roots_dom & Hpriv2 & Hpriv3); by apply map_disjoint_dom.
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

Lemma ensure_in_χ_pub χ ℓ : lloc_map_inj χ → exists χ' γ, lloc_map_mono χ χ' ∧ χ' !! γ = Some (LlocPublic ℓ) ∧ ∀ γ' r, γ' ≠ γ → χ' !! γ' = r → χ !! γ' = r.
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

Definition extended_to (χold : lloc_map) (ζ : lstore) (χnew : lloc_map) :=
  lloc_map_mono χold χnew ∧ dom χold ## dom ζ ∧ is_private_blocks χnew ζ.

Lemma extended_to_inj χ1 ζ χ2 : extended_to χ1 ζ χ2 → lloc_map_inj χ2.
Proof.
  intros (H&_); apply H.
Qed.

Lemma extended_to_dom_subset χ1 ζ χ2 : extended_to χ1 ζ χ2 → dom ζ ⊆ dom χ2.
Proof.
  intros (H1&H2&H3).
  eapply elem_of_subseteq. intros γ Hx; eapply elem_of_dom_2. by apply H3.
Qed.

Definition allocate_in_χ_priv (χold : lloc_map) v : lloc_map_inj χold → exists χnew γ, extended_to χold {[γ := v]} χnew.
Proof.
  intros Hinj.
  eexists (<[fresh (dom χold) := LlocPrivate]> χold), (fresh (dom χold)).
  unfold extended_to; split_and!; first split.
  - eapply insert_subseteq, not_elem_of_dom, is_fresh.
  - intros γ1 γ2 ℓ' [[? ?]|[? ?]]%lookup_insert_Some [[? ?]|[? ?]]%lookup_insert_Some; subst; try congruence.
    by eapply Hinj.
  - rewrite dom_singleton_L. eapply disjoint_singleton_r. by apply is_fresh.
  - intros x. rewrite dom_singleton_L. intros ->%elem_of_singleton.
    eapply lookup_insert.
Qed.

Lemma disjoint_strengthen T `{Countable T} (A1 A2 B1 B2 : gset T) : A1 ## B1 → A2 ⊆ A1 → B2 ⊆ B1 → A2 ## B2.
Proof.
  intros HD H1 H2.
  apply elem_of_disjoint.
  intros x HA HB.
  edestruct (@elem_of_disjoint) as [HL _]; eapply HL.
  - apply HD.
  - eapply elem_of_weaken; first apply HA. done.
  - eapply elem_of_weaken; first apply HB. done.
Qed.

Lemma extended_to_trans (χ1 χ2 χ3 : lloc_map) (ζ1 ζ2 : lstore) : 
  extended_to χ1 ζ1 χ2 →
  extended_to χ2 ζ2 χ3 →
  extended_to χ1 (ζ1 ∪ ζ2) χ3 /\ ζ1 ##ₘ ζ2.
Proof.
  intros (HA1 & HA2 & HA3) (HB1 & HB2 & HB3). unfold extended_to; split_and!.
  - split; last apply HB1. etransitivity; first apply HA1; apply HB1.
  - erewrite dom_union_L. eapply disjoint_union_r. split; first done.
    eapply disjoint_strengthen. 1: apply HB2. 2: done. apply subseteq_dom, HA1.
  - intros γ. rewrite dom_union_L. intros [H|H]%elem_of_union; last by apply HB3.
    eapply lookup_weaken; first by apply HA3.
    apply HB1.
  - eapply map_disjoint_dom. eapply disjoint_strengthen. 1: apply HB2. 2: done.
    eapply extended_to_dom_subset; done.
Qed.

Lemma extended_to_trans_2 (χ1 χ2 χ3 : lloc_map) (ζ1 ζ2 : lstore) : 
  extended_to χ1 ζ1 χ2 →
  extended_to χ2 ζ2 χ3 →
  extended_to χ1 (ζ2 ∪ ζ1) χ3 /\ ζ1 ##ₘ ζ2.
Proof.
  intros H1 H2.
  destruct (extended_to_trans χ1 χ2 χ3 ζ1 ζ2) as (H3&H4). 1-2: done.
  erewrite map_union_comm; done.
Qed.

Lemma extended_to_refl χ1 :
  lloc_map_inj χ1 →
  extended_to χ1 ∅ χ1.
Proof.
  by repeat split.
Qed.

Lemma extended_to_mono χ1 χ2 :
  lloc_map_mono χ1 χ2 →
  extended_to χ1 ∅ χ2.
Proof.
  intros (H1 & H2); by repeat split.
Qed.

Lemma is_val_extended_to_weaken χ1 χ2 ζ1 ζ2 v lv:
  is_val χ1 ζ1 v lv →
  extended_to χ1 ζ2 χ2 →
  is_val χ2 (ζ1 ∪ ζ2) v lv.
Proof.
  intros H1 (H21&H22&H23).
  eapply is_val_mono; last done.
  1: apply H21.
  apply map_union_subseteq_l.
Qed.

Lemma deserialize_ML_value χMLold v :  
  lloc_map_inj χMLold
→ ∃ χC ζimm lv,
    extended_to χMLold ζimm χC
  ∧ is_val χC ζimm v lv.
Proof.
  induction v as [[x|bo| |ℓ]| |v1 IHv1 v2 IHv2|v IHv|v IHv] in χMLold|-*; intros Hinj.
  1-3,5: eexists χMLold, ∅, _; split_and!; [by eapply extended_to_refl | econstructor ].
  Unshelve. 5: exact (Lloc 0). (* what happens for functions *)
  - destruct (ensure_in_χ_pub χMLold ℓ) as (χ' & γ & Hχ' & Hγ & _); first done.
    exists χ', ∅, (Lloc γ); (split_and!; last by econstructor).
    by eapply extended_to_mono.
  - destruct (IHv1 χMLold) as (χ1 & ζ1 & lv1 & Hext1 & Hlv1); first done.
    destruct (IHv2 χ1) as (χ2 & ζ2 & lv2 & Hext2 & Hlv2); first by eapply extended_to_inj.
    pose (Immut,(TagDefault,[lv1;lv2])) as blk.
    edestruct (allocate_in_χ_priv χ2 blk) as (χ3 & γ & Hext3); first by eapply extended_to_inj.
    eassert (extended_to χMLold _ χ3).
    1: do 2 (eapply extended_to_trans; last done); done.
    do 3 eexists; split; first done.
    econstructor.
    + rewrite lookup_union_r; first by erewrite lookup_singleton.
      eapply map_disjoint_Some_r. 1: eapply extended_to_trans_2; first eapply extended_to_trans; done.
      apply lookup_singleton.
    + eapply is_val_extended_to_weaken; last done.
      eapply is_val_extended_to_weaken; done.
    + eapply is_val_extended_to_weaken; last done.
      eapply is_val_mono; last done; try done.
      eapply map_union_subseteq_r. eapply extended_to_trans; done.
  - destruct (IHv χMLold) as (χ1 & ζ1 & lv1 & Hext1 & Hlv1); first done.
    epose (Immut,(_,[lv1])) as blk.
    edestruct (allocate_in_χ_priv χ1 blk) as (χ3 & γ & Hext3); first by eapply extended_to_inj.
    eassert (extended_to χMLold _ χ3).
    1: (eapply extended_to_trans; last done); done.
    do 3 eexists; split; first done.
    econstructor.
    + rewrite lookup_union_r; first by erewrite lookup_singleton.
      eapply map_disjoint_Some_r. 1: eapply extended_to_trans_2; done.
      apply lookup_singleton.
    + eapply is_val_extended_to_weaken; done.
  - destruct (IHv χMLold) as (χ1 & ζ1 & lv1 & Hext1 & Hlv1); first done.
    epose (Immut,(_,[lv1])) as blk.
    edestruct (allocate_in_χ_priv χ1 blk) as (χ3 & γ & Hext3); first by eapply extended_to_inj.
    eassert (extended_to χMLold _ χ3).
    1: (eapply extended_to_trans; last done); done.
    do 3 eexists; split; first done.
    econstructor.
    + rewrite lookup_union_r; first by erewrite lookup_singleton.
      eapply map_disjoint_Some_r. 1: eapply extended_to_trans_2; done.
      apply lookup_singleton.
    + eapply is_val_extended_to_weaken; done.
Qed.

Lemma deserialize_ML_values χMLold vs :  
  lloc_map_inj χMLold
→ ∃ χC ζimm lvs,
    extended_to χMLold ζimm χC
  ∧ Forall2 (is_val χC ζimm) vs lvs.
Proof.
  induction vs as [|v vs IH] in χMLold|-*; intros Hinj.
  - eexists χMLold, ∅, _; split_and!; [by eapply extended_to_refl | econstructor ].
  - destruct (deserialize_ML_value χMLold v Hinj) as (χ1 & ζ1 & lv & Hext1 & Hlv1).
    destruct (IH χ1) as (χ2 & ζ2 & lvs & Hext2 & Hlv2); first by eapply extended_to_inj.
    eassert (extended_to χMLold _ χ2) by by eapply extended_to_trans.
    eexists _, _, (lv::lvs). split_and!; first done.
    econstructor.
    + by eapply is_val_extended_to_weaken.
    + eapply Forall2_impl; first done.
      intros v' lv' H1. eapply is_val_mono; last done; try done.
      eapply map_union_subseteq_r, extended_to_trans; done.
Qed.

Lemma deserialize_ML_block χMLold vs :  
  lloc_map_inj χMLold
→ ∃ χC ζimm blk,
    extended_to χMLold ζimm χC
  ∧ is_heap_elt χC ζimm vs blk.
Proof.
  intros H.
  destruct (deserialize_ML_values χMLold vs H) as (χC & ζimm & lvs & H1 & H2).
  by exists χC, ζimm, (Mut,(TagDefault,lvs)).
Qed.


Lemma is_store_blocks_mono_weaken χ1 χ2 ζ σ:
  is_store_blocks χ1 ζ σ →
  lloc_map_mono χ1 χ2 →
  is_store_blocks χ2 ζ σ.
Proof.
  intros (H1&H2) [Hsub H3]. split.
  - intros x Hx. destruct (H1 x Hx) as [y Hy]; exists y.
    eapply lookup_weaken; done.
  - intros γ; destruct (H2 γ) as [H2L H2R]; split.
    + intros H; destruct (H2L H) as (ℓ&Vs&HH1&HH2). do 2 eexists; repeat split; try done.
      eapply lookup_weaken; done.
    + intros (ℓ&Vs&HH1&HH2).
      apply H2R. do 2 eexists; repeat split; try done.
      destruct (H1 ℓ) as (γ2&Hγ2); first by eapply elem_of_dom_2.
      rewrite <- Hγ2.
      eapply lookup_weaken in Hγ2; last done.
      f_equiv. eapply H3; done.
Qed.

Lemma is_heap_elt_weaken χ ζ vs blk ζ' χ' :
  is_heap_elt χ ζ vs blk
→ χ ⊆ χ'
→ ζ ⊆ ζ'
→ is_heap_elt χ' ζ' vs blk.
Proof.
  intros H1 H2 H3.
  inversion H1; subst.
  econstructor. eapply Forall2_impl; first done.
  intros x y H4; eapply is_val_mono; last done. all:done.
Qed.

Lemma is_heap_elt_weaken_2 χ ζ vs blk ζ' χ' :
  is_heap_elt χ ζ vs blk
→ extended_to χ' ζ χ
→ dom ζ' ⊆ dom χ'
→ is_heap_elt χ (ζ' ∪ ζ) vs blk.
Proof.
  intros H1 H2 H3.
  eapply is_heap_elt_weaken. 1: done.
  1: done. eapply map_union_subseteq_r.
  eapply map_disjoint_dom. eapply disjoint_strengthen.
  1: apply H2. 1-2:done.
Qed.

Lemma deserialize_ML_heap χMLold σ : 
  lloc_map_inj χMLold
→ ∃ χC ζσ ζnewimm,
    extended_to χMLold ζnewimm χC
  ∧ is_store_blocks χC σ ζσ
  ∧ is_store χC (ζσ ∪ ζnewimm) σ.
Proof.
  revert χMLold.
  induction σ as [|ℓ [vv|] σ Hin IH] using map_ind; intros χMLold HχMLold .
  - exists χMLold, ∅, ∅; split_and!. 2: econstructor.
    + by eapply extended_to_refl.
    + intros γ; rewrite dom_empty_L; done.
    + split; rewrite dom_empty_L. 1: done.
      intros (ℓ & Vs & H1 & H2). exfalso. rewrite lookup_empty in H2. done.
    + intros ℓ Vs γ blk Hc. exfalso. rewrite lookup_empty in Hc. done.
  - destruct (IH χMLold) as (χ0 & ζσ & ζi0 & Hext & Hstbl & Hstore). 1: done.
    destruct (ensure_in_χ_pub χ0 ℓ) as (χ1 & γ & Hχ1 & Hγ & Hold); first by eapply extended_to_inj.
    apply extended_to_mono in Hχ1.
    destruct (deserialize_ML_block χ1 vv) as (χ2 & ζi2 & lvs & Hext2 & Helt); first by eapply extended_to_inj.
    edestruct (extended_to_trans) as (HextA&Hdisj1). 1: exact Hext. 1: eapply extended_to_trans; done.
    rewrite map_empty_union in Hdisj1.
    rewrite map_empty_union in HextA.
    assert (is_store_blocks χ2 (<[ℓ:=Some vv]> σ) (<[γ:=lvs]> ζσ)) as Hstore2.
    1: {eapply is_store_blocks_restore_loc.
        * eapply is_store_blocks_mono_weaken; first done. eapply extended_to_trans; done.
        * apply Hext2.
        * eapply lookup_weaken. 1: done. apply Hext2.
        * by right. }
    assert (dom (<[γ:=lvs]> ζσ ∪ ζi0) ⊆ dom χ1) as Hsub3.
    { rewrite dom_union_L. eapply union_subseteq. split.
      * rewrite dom_insert_L. apply union_subseteq. split.
        eapply singleton_subseteq_l; first by eapply elem_of_dom_2.
        eapply elem_of_subseteq; intros k Hk.
        destruct Hstbl as (HH1&HH2). apply HH2 in Hk. destruct Hk as (?&?&H1&H2).
        eapply elem_of_dom_2. eapply lookup_weaken; first apply H1.
        eapply Hχ1.
      * etransitivity; last eapply subseteq_dom, Hχ1.
        eapply extended_to_dom_subset; done. }
    eexists χ2, (<[γ := lvs]> ζσ), (ζi0 ∪ ζi2). split_and!. 1-2:done.
    + intros ℓ' vs γ' blk H1 H2 H3.  destruct HextA as (HH1&HH2&HH3).
      apply lookup_union_Some in H3. 1: destruct H3 as [H3|H3].
      3: { eapply map_disjoint_dom; eapply elem_of_disjoint.
           intros x Hx1 Hx2; specialize (HH3 x Hx2). destruct Hstore2 as [HHL HHR].
           apply HHR in Hx1. destruct Hx1 as (l1 & Vs1 & ? & ?); congruence. }
      2: { rewrite HH3 in H2; last by eapply elem_of_dom_2. congruence. }
      apply lookup_insert_Some in H3. destruct H3 as [[? ?]|[Hne H3]].
      * subst. rewrite map_union_assoc.
        eapply lookup_weaken in Hγ. 2: eapply Hext2. rewrite Hγ in H2. injection H2; intros ->.
        rewrite lookup_insert in H1. injection H1; intros ->.
        by eapply is_heap_elt_weaken_2.
      * eapply lookup_insert_Some in H1. destruct H1 as [[-> H]|[Hne1 H1]].
        1: {exfalso. apply Hne. eapply HH1. 2: done. eapply lookup_weaken; first done. apply Hext2. }
        assert (χ0 !! γ' = Some (LlocPublic ℓ')) as H2'.
        1: {destruct Hstbl as [HHL HHR]. destruct (HHL ℓ') as (gg&Hgg); first by eapply elem_of_dom_2.
            rewrite <- Hgg; f_equal. eapply HH1. 1: done. eapply lookup_weaken; first done. etransitivity; last eapply Hext2; eapply Hχ1. }
        eapply is_heap_elt_weaken.
        1: eapply Hstore. 1: done. 3: etransitivity; first eapply Hχ1; last apply Hext2.
        2: erewrite lookup_union_l; first done. 1: done.
        1: eapply not_elem_of_dom; intros H; eapply Hext in H; congruence.
        etransitivity; first eapply map_union_mono_l.
        2: etransitivity; first eapply map_union_mono_r. 4: done.
        1: eapply map_union_subseteq_l.
        1: eapply is_store_blocks_is_private_blocks_disjoint; done.
        eapply insert_subseteq, not_elem_of_dom.
        intros H. destruct Hstbl as [HHL HHR]. eapply HHR in H.
        destruct H as (?&?&Heq1&HeqF). eapply lookup_weaken in Heq1; first erewrite Hγ in Heq1. 2: apply Hχ1.
        injection Heq1; intros ->; rewrite HeqF in Hin; congruence.
  - destruct (IH χMLold) as (χ0 & ζσ & ζi0 & Hext & Hstbl & Hstore). 1: done.
    destruct (ensure_in_χ_pub χ0 ℓ) as (χ1 & γ & Hχ1 & Hγ & Hold); first by eapply extended_to_inj.
    edestruct (extended_to_trans) as (HextA&Hdisj1); first exact Hext. 1: eapply extended_to_mono, Hχ1.
    exists χ1, ζσ, ζi0. split_and!. 2: destruct Hstbl as [HL HR]; split.
    + rewrite map_union_empty in HextA. done.
    + rewrite dom_insert_L. intros ℓ0 [->%elem_of_singleton|H]%elem_of_union.
      1: eexists; done.
      destruct (HL ℓ0 H) as (γ1&Hγ1). exists γ1; eapply lookup_weaken; first done.
      eapply Hχ1.
    + intros γ0; specialize (HR γ0) as (HRL&HRR). split.
      1: intros H; destruct (HRL H) as (ℓ0 & Vs & H3 & H5); do 2 eexists;
        split; first (eapply lookup_weaken; first done; eapply Hχ1);
        rewrite lookup_insert_ne; first done;
        intros ->; rewrite Hin in H5; congruence.
      intros (ℓ0&Vs&HH1&HH2).
      rewrite lookup_insert_Some in HH2; destruct HH2 as [[? ?]|[Hne HH2]].
      1: congruence.
      eapply HRR. eexists ℓ0, Vs. split; last done.
      eapply elem_of_dom_2 in HH2.
      destruct (HL ℓ0 HH2) as (γ1&Hγ1). rewrite <- Hγ1. f_equal.
      eapply Hχ1; try done. eapply lookup_weaken, Hχ1; done.
    + intros ℓ1 vs γ1 blk [[? ?]|[? H1]]%lookup_insert_Some H2 H3; try congruence.
      eapply is_heap_elt_weaken. 1: eapply Hstore; try done.
      3: done. 2: eapply Hχ1.
      destruct Hstbl as [HHL HHR].
      destruct (HHL ℓ1) as (k1&Hk1); first by eapply elem_of_dom_2.
      rewrite <- Hk1. f_equal. eapply Hχ1; try done. eapply lookup_weaken, Hχ1; done.
Qed.

Lemma deserialize_ML_heap_extra ζMLold χMLold σ : 
  lloc_map_inj χMLold
→ dom ζMLold ⊆ dom χMLold
→ (map_Forall (fun _ ℓ => σ !! ℓ = Some None) (pub_locs_in_lstore χMLold ζMLold))
→ ∃ χC ζσ ζnewimm,
    extended_to χMLold ζnewimm χC
  ∧ is_store_blocks χC σ ζσ
  ∧ ζMLold ##ₘ (ζσ ∪ ζnewimm)
  ∧ is_store χC (ζMLold ∪ ζσ ∪ ζnewimm) σ.
Proof.
  intros H1 H2 H3.
  destruct (deserialize_ML_heap χMLold σ) as (χC&ζσ&ζi&HA1&HA2&HA3). 1: apply H1.
  assert (ζMLold ##ₘ ζσ ∪ ζi) as Hdisj.
  1: eapply map_disjoint_union_r; split; last (eapply map_disjoint_dom, disjoint_strengthen; first apply HA1; done).
  1: { eapply map_disjoint_spec. intros γ b1 b2 HH1 HH2.
       destruct HA2 as [_ HA2R]. eapply elem_of_dom_2 in HH2. apply HA2R in HH2.
       destruct HH2 as (ℓ & Vs & HH7 & HH8).
       erewrite (map_Forall_lookup_1 _ _ _ _ H3) in HH8.
       2: { eapply elem_of_dom_2 in HH1. erewrite pub_locs_in_lstore_lookup; first done; first done.
            eapply elem_of_weaken in H2; last done.
            eapply elem_of_dom in H2; destruct H2 as [k Hk]. rewrite Hk. 
            eapply lookup_weaken in Hk; first erewrite HH7 in Hk. 2: eapply HA1. done. }
       congruence. }
  do 3 eexists; split_and!; try done.
  - intros ℓ vs γ b He1 He2 He3.
    eapply is_heap_elt_weaken. 1: eapply HA3; try done. 2: done.
    + rewrite <- map_union_assoc in He3. eapply lookup_union_Some in He3; destruct He3; try done.
      destruct (HA2) as [HL HR]. destruct (HR γ) as [HRL HRR]. eapply elem_of_dom in HRR. destruct HRR as [vv Hvv].
      2: do 2 eexists; done.
      exfalso. erewrite map_disjoint_Some_r in H; try congruence. 1: done.
      erewrite lookup_union_Some_l; last done; first done.
    + erewrite <- map_union_assoc. eapply map_union_subseteq_r. done.
Qed.

Lemma collect_dom_θ_vs (θdom : gset lloc) (vs : list lval) : exists θdom' : gset lloc, forall γ, (Lloc γ ∈ vs ∨ γ ∈ θdom) ↔ γ ∈ θdom'.
Proof.
  induction vs as [|[|ℓ] vs (θdom1 & IH)].
  - exists θdom. intros γ. split; last eauto. intros [[]%not_elem_of_nil|?]; done.
  - exists θdom1. intros γ. split.
    + intros [[Hc|H]%elem_of_cons|?]; try congruence; apply IH. 1: by left. by right.
    + intros [H|H]%IH; last by right. left. right. done.
  - exists (θdom1 ∪ {[ ℓ ]}). intros γ. split.
    + intros [[Hc|H]%elem_of_cons|?]; eapply elem_of_union. 1: right; eapply elem_of_singleton; congruence.
      all: left; apply IH. 1: by left. by right.
    + intros [[H|H]%IH| ->%elem_of_singleton]%elem_of_union. 1: left; right; done. 1: right; done.    
      left; left; done.
Qed.

Lemma collect_dom_θ_ζ_blocks (θdom : gset lloc) (ζ : lstore) : exists θdom' : gset lloc,
    forall γ, ((exists γ1 m t vs, ζ !! γ1 = Some (m, (t, vs)) ∧ Lloc γ ∈ vs) ∨ γ ∈ θdom) ↔ γ ∈ θdom'.
Proof.
  induction ζ as [|k [m [t vs]] ζ Hne (θdom1 & Hdom1)] using map_ind.
  - exists θdom; split.
    + intros [(γ1&m&t&vs&H1&H2)|Hold]; last done.
      rewrite lookup_empty in H1; done.
    + intros H; by right.
  - destruct (collect_dom_θ_vs θdom1 vs) as (θdom2 & Hdom2).
    exists θdom2. intros γ; split.
    + intros [(γ1&m'&t'&vs'&[[-> Hinj]|[Hne2 Hin]]%lookup_insert_Some&H2)|Hold].
      1: apply Hdom2; left; congruence.
      1: apply Hdom2; right; apply Hdom1; left; by repeat eexists.
      1: apply Hdom2; right; apply Hdom1; right; done.
    + intros [H|[(γ1&m'&t'&vs'&H1&H2)|H]%Hdom1]%Hdom2.
      1: left; do 4 eexists; split; first eapply lookup_insert; done.
      2: by right.
      left; do 4 eexists; split; last done; first rewrite lookup_insert_ne; first done.
      intros ->; rewrite Hne in H1; congruence.
Qed.

Lemma collect_dom_θ_ζ (θdom : gset lloc) (ζ : lstore) : exists θdom' : gset lloc,
    forall γ, (γ ∈ dom ζ ∨ (exists γ1 m t vs, ζ !! γ1 = Some (m, (t, vs)) ∧ Lloc γ ∈ vs) ∨ γ ∈ θdom) ↔ γ ∈ θdom'.
Proof.
  destruct (collect_dom_θ_ζ_blocks θdom ζ) as (θdom1 & Hdom1).
  exists (dom ζ ∪ θdom1). intros γ; split.
  - (intros [H|H]; apply elem_of_union); first by left.
    right; apply Hdom1; done.
  - intros [H|H]%elem_of_union; first by left. right; by apply Hdom1.
Qed.

Lemma collect_dom_θ_roots (θdom : gset lloc) (roots : roots_map) : exists θdom' : gset lloc,
    forall γ, ((exists k, roots !! k = Some (Lloc γ)) ∨ γ ∈ θdom) ↔ γ ∈ θdom'.
Proof.
  induction roots as [|k [z|l] roots Hne (θdom1 & IH)] using map_ind.
  - exists θdom. intros γ. split; last eauto. intros [[? H%lookup_empty_Some]|?]; done.
  - exists θdom1. intros γ. split.
    + intros [[k1 [[-> ?]|[H1 H2]]%lookup_insert_Some]|?]; try congruence; apply IH. 2: by right. left. by eexists.
    + intros [[k' Hk]|H]%IH; last by right. left. exists k'. rewrite lookup_insert_ne; first done. intros ->; rewrite Hne in Hk; done.
  - exists (θdom1 ∪ {[ l ]}). intros γ. split.
    + intros [[k1 [[-> ?]|[H1 H2]]%lookup_insert_Some]|?]; try congruence; eapply elem_of_union. 1: right; eapply elem_of_singleton; congruence.
      all: left; apply IH. 2: by right. left; by eexists.
    + intros [[[k' Hk]|H]%IH| ->%elem_of_singleton]%elem_of_union. 2: by right. 2: left; exists k; by rewrite lookup_insert.
      left; exists k'; rewrite lookup_insert_ne; first done. intros ->; rewrite Hne in Hk; congruence.
Qed.

Lemma injectivify_map (S : gset lloc) : exists M : addr_map, dom M = S ∧ gmap_inj M.
Proof.
  induction S as [|s S Hne (M & <- & Hinj)] using set_ind_L.
  - exists ∅; split; first by rewrite dom_empty_L. intros ??? H1; exfalso. rewrite lookup_empty in H1; done.
  - exists (<[s := fresh (codom M)]> M). split.
    1: by rewrite dom_insert_L.
    apply gmap_inj_extend; try done.
    intros k' v' H%codom_spec_2 <-. unshelve eapply is_fresh; last exact H. all: apply _.
Qed.

Lemma find_repr_lval_vv θ v : 
   (forall γ, Lloc γ = v → γ ∈ dom θ)
 → exists l, repr_lval θ v l.
Proof.
  intros H. destruct v as [z|a].
  - eexists; by econstructor.
  - destruct (θ !! a) as [va|] eqn:Heq.
    2: eapply not_elem_of_dom in Heq; exfalso; apply Heq; apply H; done.
    eexists; econstructor; apply Heq.
Qed.

Lemma find_repr_lval_vs θ vs : 
   (forall γ, Lloc γ ∈ vs → γ ∈ dom θ)
 → exists ls, Forall2 (repr_lval θ) vs ls.
Proof.
  intros H; induction vs as [|v vs IH] in H|-*.
  - exists nil. econstructor.
  - destruct IH as [ls IH]; first (intros γ Hγ; eapply H; right; done).
    destruct (find_repr_lval_vv θ v) as [l Hl].
    1: intros γ <-; apply H; by left.
    eexists. econstructor; done.
Qed.

Lemma find_repr_roots θ roots privmem : 
   roots_are_live θ roots
 → dom privmem ## dom roots
 → exists mem, repr θ roots privmem mem.
Proof.
  revert privmem. unfold repr.
  induction roots as [|l a roots_m Hin IH] using map_ind; intros privmem Hlive Hdisj.
  - exists privmem, ∅. split_and!.
    + econstructor.
    + eapply map_disjoint_empty_r.
    + by rewrite map_empty_union.
  - destruct (IH privmem) as (mem1 & memr1 & Hrepr1 & Hdisj1 & Heq1).
    1: { intros a1 w1 H1; eapply Hlive; rewrite lookup_insert_ne; first done.
         intros ->; rewrite Hin in H1; congruence. }
    1: rewrite dom_insert_L in Hdisj; set_solver.
    destruct (find_repr_lval_vv θ a) as (w & Hw).
    1: intros γ <-; eapply Hlive; apply lookup_insert.
    exists (<[l:=Storing w]> mem1), (<[l:=Storing w]> memr1). split_and!.
    + econstructor. 1: done. 1:done. 2: erewrite <- repr_roots_dom; last apply Hrepr1. all: by eapply not_elem_of_dom.
    + apply map_disjoint_dom in Hdisj1. apply map_disjoint_dom.
      rewrite dom_insert_L. rewrite dom_insert_L in Hdisj. set_solver.
    + erewrite Heq1. now rewrite insert_union_l.
Qed.


Lemma set_to_some θ mem roots_m privmem :
    repr θ roots_m privmem mem
 -> gen_heap_interp (privmem ∪ ((λ _ : lval, None) <$> roots_m))
 -∗ ([∗ set] a0 ∈ dom roots_m, a0 O↦ None)
 ==∗ gen_heap_interp mem
     ∗ ([∗ map] a0↦v0 ∈ roots_m, ∃ w, a0 ↦C{DfracOwn 1} w ∗ ⌜repr_lval θ v0 w⌝).
Proof.
  intros (mm & Hrepr1 & Hrepr2 & Hrepr3).
  induction Hrepr1 in Hrepr2,Hrepr3,mem,privmem|-*.
  + iIntros "Hheap Hset !>".
    rewrite fmap_empty. rewrite dom_empty_L. rewrite map_union_empty.
    rewrite map_empty_union in Hrepr3. subst mem. iFrame.
    iApply big_sepM_empty. done.
  + eapply not_elem_of_dom in H0,H1. iIntros "Hheap Hset".
    rewrite dom_insert_L.
    iPoseProof (big_sepS_insert) as "(Hb1 & _)"; first eapply not_elem_of_dom_2, H0.
    iPoseProof ("Hb1" with "Hset") as "(Hw & Hset)".
    rewrite fmap_insert. rewrite <- insert_union_r.
    2: eapply map_disjoint_Some_r; first done; by rewrite lookup_insert.
    iMod (gen_heap_update _ _ _ (Storing w) with "Hheap Hw") as "(Hheap & Hw)".
    rewrite insert_insert.
    rewrite insert_union_l.
    iMod (IHHrepr1 with "Hheap Hset") as "(Hheap & Hset)".
    * eapply map_disjoint_insert_l_2; first done.
      erewrite <- (delete_insert mem0); last done.
      by eapply map_disjoint_delete_r.
    * done.
    * rewrite <- insert_union_r; last done.
      subst mem. rewrite insert_union_l. iModIntro.
      iFrame.
      iApply (big_sepM_insert_2 with "[Hw] Hset").
      iExists w. iFrame. done.
Qed.

Lemma zip_args_length a b : length a = length b → exists v, C_lang.zip_args a b = Some v.
Proof.
  intros Hlen.
  assert (Forall2 (fun _ _ => True) a b) as Hforall by by apply Forall2_true.
  clear Hlen. induction Hforall as [|[|s] ar bx br _ Hforall [v IH]].
  - cbn. eexists _; done.
  - cbn. eexists; apply IH.
  - eexists. cbn. rewrite IH. cbn. done.
Qed.

Lemma apply_function_arity F ws : arity F = length ws → ∃ k, C_lang.apply_function F ws = Some k.
Proof.
  intros H. destruct F as [c args]. cbn in H|-*.
  destruct (zip_args_length c ws) as [σ Hσ]; first done.
  eexists; rewrite Hσ. done.
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

  iSplitR.
  + iPureIntro. exists (fun _ => True). eapply mlanguage.head_prim_step. cbn.

    destruct (deserialize_ML_heap_extra (ζML ρml) (χML ρml) σ) as (χ1 & ζσ & ζσimm & Hext & Hstorebl & Hdisj & Hstore).
    1: done.
    1: eapply elem_of_subseteq; done.
    1: done.
    destruct (deserialize_ML_values χ1 vv) as (χ2 & ζimm & lvs & Hext2 & Hvs).
    1: apply Hext.

    assert (ζML ρml ∪ ζσ ∪ ζσimm ##ₘ ζimm) as Hdis1.
    1: { eapply map_disjoint_dom. eapply disjoint_strengthen. 1: eapply Hext2. 2: done.
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
    destruct (apply_function_arity F ws) as (ec & Hec).
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
         eapply map_disjoint_dom, disjoint_strengthen; first eapply map_disjoint_dom, Hdis1; try done.
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
    * iApply (wp_simulates with "Hnb"); iApply ("Hwp" with "[- ] [] [] Hsim"); try done.
      unfold GC; cbn.
      iExists (dom (rootsML ρml)), (rootsML ρml).
      iFrame "HAGCθ HAGCbound HArootss HArootsm Hrootspto". done.
Qed.

End Simulation.
