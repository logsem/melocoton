From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem wrapperstate.
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
    rewrite <- (lookup_union_r memr privmem); try done; unfold C_lang.state in Hunion; rewrite <- Hunion; by apply lookup_delete.
    eexists privmem, (<[l:=Storing w]> memr). split_and!.
    * econstructor; try done; by eapply not_elem_of_dom.
    * by apply map_disjoint_insert_r.
    * unfold C_lang.state in * |- *. erewrite <- insert_union_l. rewrite <- Hunion. rewrite insert_delete_insert.
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
    * subst mem. unfold C_lang.state. erewrite <- insert_union_l.
      rewrite insert_insert. by rewrite insert_union_r.
    * iModIntro. iSplitL "Hheap".
      - unfold C_lang.state. erewrite <- insert_union_l. rewrite insert_union_r.
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
  1: iApply (block_sim_to_ghost_state with "HAχbij HAζbl"); done.
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
  iAssert (⌜gmap_inj χvirt⌝)%I as "%Hinj".
  1: { iPoseProof (gset_bij_own_valid with "HAχbij") as "%Hbij". iPureIntro.
       destruct Hbij as (_ & Hbij). intros l1 l2 vv Hl1 Hl2.
       eapply gset_bijective_eq_iff. 1: apply Hbij.
       1-2: eapply elem_of_map_to_set_pair. all: done. }
  iMod (set_to_none with "HσC Hrootspto") as "(HσC & Hrootspto)".
  1: done.

  do 3 iModIntro. do 2 iExists _.  iSplit.
  1: iPureIntro; eapply (H4 σMLvirt l v ζfreeze ζσ χvirt ζrest roots_m privmem).
  all: try done.
  1: rewrite map_union_comm; done.
  1: apply map_disjoint_dom_1; eapply map_disjoint_spec; intros ?????; by eapply map_disjoint_spec.

  iSplitR "Hv Hnb"; last first.
  1: { iApply weakestpre.wp_value'. iFrame. }
  cbn. iSplitL "HAσMLv HAnMLv".
  1: iExists nMLv; iFrame.
  unfold private_state_interp, ML_state_interp, GC_token_remnant, named; cbn.
  iExists ζσ, ζfreeze, fresh.
  iFrame "HArootss".
  iFrame "HAGCθ".
  iFrame "HAζbl".
  iSplitL "HσC HnC"; first (iExists nCv; iFrame).
  iFrame "HAχbij".
  iFrame "HAfresh".
  iFrame "HAχNone".
  iFrame "HAζpers".
  iFrame "Hbound".
  iFrame "HAθ".
  rewrite <- Hagree2.
  iFrame "HAroots".
  iFrame "Hrootspto".
  iFrame "HArootsm".
  done.
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
    iExists ζfreeze, ζσ, ζrest, χvirt, fresh, σMLvirt.
    iFrame. iFrame "HAζpers".
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
      unfold C_state_interp, named. iExists ζfreeze, ζσ, ζrest, χvirt, fresh, σMLvirt.
      iFrame. iFrame "HAζpers". iSplitL; first by iExists _.
      iPureIntro; split_and!; done.
Qed.


Definition is_store_blocks_proto (χ : lloc_map) (σ : store) (ζ : gset lloc) : Prop :=
  dom σ = dom χ ∧
  (∀ γ, γ ∈ ζ ↔ ∃ ℓ Vs, χ !! ℓ = Some γ ∧ σ !! ℓ = Some (Some Vs)).

Lemma find_new_chi_zeta χin σ (forbidS : gset lloc):
    dom χin ⊆ dom σ
  → gmap_inj χin
  → ∃ χC ζσ, 
      lloc_map_mono χin χC 
    ∧ is_store_blocks_proto χC σ ζσ
    ∧ forall x y, χC !! x = Some y → y ∈ forbidS → χin !! x = Some y.
Proof.
  revert χin forbidS.
  induction σ as [ | ℓ vo σ Hnone IH] using map_ind; intros χin forbidS Hsub Hinj.
  - rewrite dom_empty_L in Hsub. apply equiv_empty_L in Hsub. apply dom_empty_inv_L in Hsub.
    subst χin. exists ∅, ∅. repeat split.
    + done.
    + unfold lloc_map. by repeat erewrite dom_empty_L.
    + intros []%elem_of_empty.
    + intros (ℓ & Vs & H1 & H2). rewrite lookup_empty in H2. congruence.
    + intros x y H. rewrite lookup_empty in H; congruence.
  - rewrite dom_insert_L in Hsub. destruct (χin !! ℓ) as [g|] eqn:Heq.
    + destruct (IH (delete ℓ χin) ({[ g ]} ∪ forbidS)) as (χC & ζσ & (Hmono1 & Hmono2) & (Hstore1 & Hstore2) & Hforbid).
      1: erewrite dom_delete_L; set_solver.
      1: { intros x y1 y2 [_ H1]%lookup_delete_Some [_ H2]%lookup_delete_Some. by eapply (Hinj x y1 y2). }
      exists (<[ ℓ := g ]> χC).
      destruct vo as [v|].
      * exists ({[g]} ∪ ζσ). repeat split.
        -- eapply delete_insert_subseteq; done.
        -- intros x1 x2 y [[? ?]|[H1ne H1]]%lookup_insert_Some [[? ?]|[H2ne H2]]%lookup_insert_Some; subst.
           1: congruence.
           1: specialize (Hforbid _ _ H2 (ltac:(set_solver)));
              apply lookup_delete_Some in Hforbid;
              eapply Hinj; try done; apply Hforbid.
           1: specialize (Hforbid _ _ H1 (ltac:(set_solver)));
              apply lookup_delete_Some in Hforbid;
              eapply Hinj; try done; apply Hforbid.
           1: eapply Hmono2; done.
        -- rewrite ! dom_insert_L. by rewrite Hstore1.
        -- intros [->%elem_of_singleton|Hin]%elem_of_union.
           ++ exists ℓ, v. by rewrite ! lookup_insert.
           ++ apply Hstore2 in Hin as Hin2.
              destruct Hin2 as (ℓ2 & v2 & HH1 & HH2).
              exists ℓ2, v2. rewrite ! lookup_insert_ne; first done.
              all: intros <-; rewrite Hnone in HH2; congruence.
        -- intros (ℓ2 & v2 & [[? ?]|[H1ne H1]]%lookup_insert_Some & [[? ?]|[H2ne H2]]%lookup_insert_Some); subst.
           ++ set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ eapply elem_of_union_r. eapply Hstore2. by do 2 eexists.
        -- intros x y [[? ?]|[H1ne H1]]%lookup_insert_Some Hin; subst.
           ++ done.
           ++ specialize (Hforbid x y H1).
              rewrite lookup_delete_ne in Hforbid; last done. apply Hforbid. set_solver.
      * exists ζσ. repeat split.
        -- eapply delete_insert_subseteq; done.
        -- intros x1 x2 y [[? ?]|[H1ne H1]]%lookup_insert_Some [[? ?]|[H2ne H2]]%lookup_insert_Some; subst.
           1: congruence.
           1: specialize (Hforbid _ _ H2 (ltac:(set_solver)));
              apply lookup_delete_Some in Hforbid;
              eapply Hinj; try done; apply Hforbid.
           1: specialize (Hforbid _ _ H1 (ltac:(set_solver)));
              apply lookup_delete_Some in Hforbid;
              eapply Hinj; try done; apply Hforbid.
           1: eapply Hmono2; done.
        -- rewrite ! dom_insert_L. by rewrite Hstore1.
        -- intros Hin.
           apply Hstore2 in Hin as Hin2.
           destruct Hin2 as (ℓ2 & v2 & HH1 & HH2).
           exists ℓ2, v2. rewrite ! lookup_insert_ne; first done.
           all: intros <-; rewrite Hnone in HH2; congruence.
        -- intros (ℓ2 & v2 & [[? ?]|[H1ne H1]]%lookup_insert_Some & [[? ?]|[H2ne H2]]%lookup_insert_Some); subst; try congruence.
           eapply Hstore2. by do 2 eexists.
        -- intros x y [[? ?]|[H1ne H1]]%lookup_insert_Some Hin; subst.
           ++ done.
           ++ specialize (Hforbid x y H1).
              rewrite lookup_delete_ne in Hforbid; last done. apply Hforbid. set_solver.
    + pose (map_to_set (fun a b => b) χin : gset lloc) as used_g.
      pose (fresh (forbidS ∪ used_g)) as g.
      pose proof (is_fresh (forbidS ∪ used_g)) as Hg. fold g in Hg.
      destruct (IH χin ({[ g ]} ∪ forbidS)) as (χC & ζσ & (Hmono1 & Hmono2) & (Hstore1 & Hstore2) & Hforbid).
      1: eapply not_elem_of_dom in Heq; set_solver.
      1: done.
      exists (<[ ℓ := g ]> χC).
      destruct vo as [v|].
      * exists ({[g]} ∪ ζσ). repeat split.
        -- by eapply insert_subseteq_r.
        -- intros x1 x2 y [[Heq1 Heq2]|[H1ne H1]]%lookup_insert_Some [[Heq3 Heq4]|[H2ne H2]]%lookup_insert_Some.
           1: congruence.
           1-2: exfalso; eapply Hg; eapply elem_of_union_r; unfold used_g; eapply elem_of_map_to_set; eexists _, y; split; last done;
                eapply Hforbid; first done; set_solver.
           1: eapply Hmono2; done.
        -- rewrite ! dom_insert_L. by rewrite Hstore1.
        -- intros [->%elem_of_singleton|Hin]%elem_of_union.
           ++ exists ℓ, v. by rewrite ! lookup_insert.
           ++ apply Hstore2 in Hin as Hin2.
              destruct Hin2 as (ℓ2 & v2 & HH1 & HH2).
              exists ℓ2, v2. rewrite ! lookup_insert_ne; first done.
              all: intros <-; rewrite Hnone in HH2; congruence.
        -- intros (ℓ2 & v2 & [[? ?]|[H1ne H1]]%lookup_insert_Some & [[? ?]|[H2ne H2]]%lookup_insert_Some); subst.
           ++ set_solver.
           ++ set_solver.
           ++ set_solver.
           ++ eapply elem_of_union_r. eapply Hstore2. by do 2 eexists.
        -- intros x y [[? ?]|[H1ne H1]]%lookup_insert_Some Hin; subst.
           ++ exfalso; eapply Hg; eapply elem_of_union_l; done.
           ++ eapply Hforbid; try done; set_solver.
      * exists ζσ. repeat split.
        -- by eapply insert_subseteq_r.
        -- intros x1 x2 y [[Heq1 Heq2]|[H1ne H1]]%lookup_insert_Some [[Heq3 Heq4]|[H2ne H2]]%lookup_insert_Some.
           1: congruence.
           1-2: exfalso; eapply Hg; eapply elem_of_union_r; unfold used_g; eapply elem_of_map_to_set; eexists _, y; split; last done;
                eapply Hforbid; first done; set_solver.
           1: eapply Hmono2; done.
        -- rewrite ! dom_insert_L. by rewrite Hstore1.
        -- intros Hin.
           apply Hstore2 in Hin as Hin2.
           destruct Hin2 as (ℓ2 & v2 & HH1 & HH2).
           exists ℓ2, v2. rewrite ! lookup_insert_ne; first done.
           all: intros <-; rewrite Hnone in HH2; congruence.
        -- intros (ℓ2 & v2 & [[? ?]|[H1ne H1]]%lookup_insert_Some & [[? ?]|[H2ne H2]]%lookup_insert_Some); subst; try congruence.
           eapply Hstore2. by do 2 eexists.
        -- intros x y [[? ?]|[H1ne H1]]%lookup_insert_Some Hin; subst.
           ++ exfalso; eapply Hg; set_solver.
           ++ eapply Hforbid; try done; set_solver.
Qed.

Lemma run_function_correct F (vv : list ML_lang.val) T p E Φ: 
    ⌜Forall (fun k => p !! k = None) forbidden_function_names⌝
 -∗ ⌜arity F = length vv⌝
 -∗ at_boundary _
 -∗ (∀ θ ll aa ec, 
       GC θ 
    -∗ ⌜C_lang.apply_function F aa = Some ec⌝
    -∗ ([∗ list] l;a ∈ ll;aa, ⌜repr_lval θ l a⌝)
    -∗ block_sim_arr vv ll
    -∗ WP ec @ (mkPeC p WP_ext_call_spec); E {{a, wrap_return Φ a }})
 -∗ WP RunFunction F vv @ (mkPeW (p : prog wrap_lang) T); E {{ v, Φ v ∗ at_boundary _}}.
Proof.
  iIntros "%Hforbid %Harity Hb Hwp".
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros (σ) "Hσ".
  unfold at_boundary; cbn. destruct σ as [ρml σ | ? ?].
  2: {iExFalso. iNamed "Hσ"; iNamed "SIC". iPoseProof (ghost_var_agree with "Hb HAbound") as "%Heq". congruence. }
  iModIntro. iRight. iRight.
  iNamed "Hσ". iNamed "SIML". iNamed "HAGCrem".
  iSplitR.
  1: { iPureIntro. exists (fun _ => True). eapply mlanguage.head_prim_step. cbn. eapply RunFunctionS; last done. all: admit. }
Admitted.

End Simulation.
