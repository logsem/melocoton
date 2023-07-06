From Coq Require Import ssreflect.
From stdpp Require Import strings gmap list.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.ml_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.c_interface Require Import defs notation.
From melocoton.interop Require Import basics prims basics_resources state.

Global Notation MLval := ML_lang.val.
Global Notation Cval := C_intf.val.

Section ChiZetaConstruction.

Definition lookup_reversed `{Countable A} {B} (m : gmap A B) (b : B) :=
  { a | m !! a = Some b }.

Definition find_in_reverse `{Countable A} `{EqDecision B} (m : gmap A B) (b : B) :
  sum (lookup_reversed m b) (lookup_reversed m b → False).
Proof.
  pose (map_to_set (fun a b' => if decide (b' = b) then Some a else None) m : gset _) as Hset.
  epose (filter (fun k => is_Some k) Hset) as Hset2.
  destruct (elements Hset2) as [|[γ|] ?] eqn:Heq.
  - right. intros (a & Ha).
    apply elements_empty_inv in Heq. apply gset_leibniz in Heq.
    eapply filter_empty_not_elem_of_L.
    2: apply Heq. 1: apply _.
    2: eapply elem_of_map_to_set.
    2: exists a, b; split; done.
    rewrite decide_True; done. Unshelve. all: apply _.
  - left. exists γ.
    assert (Some γ ∈ Hset2) as Hin.
    1: eapply elem_of_elements; rewrite Heq; left.
    eapply elem_of_filter in Hin. destruct Hin as [_ Hin].
    eapply elem_of_map_to_set in Hin.
    destruct Hin as (i & b' & H1 & H2).
    destruct decide; congruence.
  - exfalso. assert (None ∈ Hset2) as Hin.
    + eapply elem_of_elements. rewrite Heq. left.
    + apply elem_of_filter in Hin. destruct Hin as [[? Hc]?]. congruence.
Qed.

Lemma find_fresh_fid (χ : lloc_map) : ∃ fid, ∀ γ' vis', χ !! γ' = Some vis' → fid ≠ lloc_visibility_fid vis'.
Proof.
  epose (fresh (lloc_map_fids χ)) as fid.
  epose proof (is_fresh (lloc_map_fids χ)) as Hfidfresh.
  fold fid in Hfidfresh.
  exists fid.
  intros γ' vis' Heq1 Heq2.
  eapply Hfidfresh. by eapply elem_of_lloc_map_fids_1.
Qed.

Lemma ensure_in_χ_pub χ ℓ :
  lloc_map_inj χ →
  ∃ χ' γ fid,
    lloc_map_mono χ χ' ∧
    χ' !! γ = Some (LlocPublic fid ℓ) ∧
    (∀ γ' r, γ' ≠ γ → χ' !! γ' = r → χ !! γ' = r).
Proof.
  intros Hinj.
  destruct (decide (ℓ ∈ lloc_map_pub_locs χ)) as [Hin|Hout].
  - eapply elem_of_lloc_map_pub_locs in Hin as (fid&γ&H).
    exists χ, γ, fid. done.
  - destruct (find_fresh_fid χ) as (fid&Hfresh).
    eexists (<[fresh (dom χ) := LlocPublic fid ℓ]> χ), _, fid. split_and!; first split.
    + eapply insert_subseteq, not_elem_of_dom, is_fresh.
    + eapply lloc_map_inj_insert_pub; try done.
      intros ?????. by eapply Hfresh.
    + by erewrite lookup_insert.
    + intros γ' ho Hne. by rewrite lookup_insert_ne.
Qed.

Lemma ensure_in_χ_fid χ id :
  lloc_map_inj χ →
  ∃ χ' γ vis,
    lloc_map_mono χ χ' ∧
    χ' !! γ = Some vis ∧
    lloc_visibility_fid vis = id ∧
    (∀ γ' r, γ' ≠ γ → χ' !! γ' = r → χ !! γ' = r).
Proof.
  intros Hinj.
  destruct (decide (id ∈ lloc_map_fids χ)) as [Hin|Hne].
  - eapply elem_of_lloc_map_fids in Hin as (γ&vis&HH1&HH2).
    exists χ, γ, vis. done.
  - eexists (<[fresh (dom χ) := LlocForeign id]> χ), _, _. split_and!; first split.
    + eapply insert_subseteq, not_elem_of_dom, is_fresh.
    + eapply lloc_map_inj_insert_foreign; try done.
      intros ?????. eapply Hne, elem_of_lloc_map_fids; eauto.
    + by erewrite lookup_insert.
    + done.
    + intros γ' ho Hne'. by rewrite lookup_insert_ne.
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
  eapply elem_of_subseteq. intros γ Hx.
  destruct (H3 γ Hx) as (y&Hy).
  by eapply elem_of_dom_2.
Qed.

Definition allocate_in_χ_priv_strong (exclusion : gset lloc) (χold : lloc_map) v : lloc_map_inj χold → exists χnew γ, extended_to χold {[γ := v]} χnew ∧ γ ∉ exclusion.
Proof.
  intros Hinj.
  pose (fresh (dom χold ∪ exclusion)) as γ.
  pose (is_fresh (dom χold ∪ exclusion)) as Hγ.
  destruct (find_fresh_fid χold) as (fid&Hfresh).
  eexists (<[γ := LlocPrivate fid]> χold), γ.
  unfold extended_to; split_and!; first split.
  - eapply insert_subseteq, not_elem_of_dom. intros HH; eapply Hγ, elem_of_union_l, HH.
  - eapply lloc_map_inj_insert_priv; first done.
    intros ?????. by eapply Hfresh.
  - rewrite dom_singleton_L. eapply disjoint_singleton_r. intros HH; eapply Hγ, elem_of_union_l, HH.
  - intros x. rewrite dom_singleton_L. intros ->%elem_of_singleton. eexists.
    eapply lookup_insert.
  - intros HH; eapply Hγ, elem_of_union_r, HH.
Qed.

Definition allocate_in_χ_priv (χold : lloc_map) v : lloc_map_inj χold → exists χnew γ, extended_to χold {[γ := v]} χnew.
Proof.
  intros Hinj. destruct (allocate_in_χ_priv_strong ∅ χold v Hinj) as (χnew&γ&H&_).
  by do 2 eexists.
Qed.

Lemma disjoint_weaken T `{Countable T} (A1 A2 B1 B2 : gset T) : A1 ## B1 → A2 ⊆ A1 → B2 ⊆ B1 → A2 ## B2.
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
    eapply disjoint_weaken. 1: apply HB2. 2: done. apply subseteq_dom, HA1.
  - intros γ. rewrite dom_union_L. intros [H|H]%elem_of_union; last by apply HB3.
    destruct (HA3 γ H) as (fid&Hfid). exists fid.
    eapply lookup_weaken; first done.
    apply HB1.
  - eapply map_disjoint_dom. eapply disjoint_weaken. 1: apply HB2. 2: done.
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
  induction v as [[x|bo| |ℓ|]| |v1 IHv1 v2 IHv2|v IHv|v IHv] in χMLold|-*; intros Hinj.
  1-3: eexists χMLold, ∅, _; split_and!; [by eapply extended_to_refl | econstructor ].
  - destruct (ensure_in_χ_pub χMLold ℓ) as (χ' & γ & fid & Hχ' & Hγ & HH); first done.
    exists χ', ∅, (Lloc γ); (split_and!; last by econstructor).
    by eapply extended_to_mono.
  - destruct (ensure_in_χ_fid χMLold id) as (χ' & γ & Hχ' & Hid & Hlu & Hvis & _); first done.
    exists χ', ∅, (Lloc γ); split_and!; last by econstructor.
    by eapply extended_to_mono.
  - destruct (allocate_in_χ_priv χMLold (Bclosure f x e)) as (χ & γ & Hextend); first done.
    eexists _, _, (Lloc γ). split; eauto. econstructor. by simplify_map_eq.
  - destruct (IHv1 χMLold) as (χ1 & ζ1 & lv1 & Hext1 & Hlv1); first done.
    destruct (IHv2 χ1) as (χ2 & ζ2 & lv2 & Hext2 & Hlv2); first by eapply extended_to_inj.
    pose (Bvblock (Immut,(TagDefault,[lv1;lv2]))) as blk.
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
    epose (Bvblock (Immut,(_,[lv1]))) as blk.
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
    epose (Bvblock (Immut,(_,[lv1]))) as blk.
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
  by exists χC, ζimm, (Bvblock (Mut,(TagDefault,lvs))).
Qed.


Lemma is_store_blocks_mono_weaken χ1 χ2 ζ σ:
  is_store_blocks χ1 ζ σ →
  lloc_map_mono χ1 χ2 →
  is_store_blocks χ2 ζ σ.
Proof.
  intros (H1&H2) [Hsub H3]. split.
  - intros x Hx. destruct (H1 x Hx) as (fid&y&Hy); exists fid,y.
    eapply lookup_weaken; done.
  - intros γ; destruct (H2 γ) as [H2L H2R]; split.
    + intros H; destruct (H2L H) as (fid&ℓ&Vs&HH1&HH2). do 3 eexists; repeat split; try done.
      eapply lookup_weaken; done.
    + intros (fid&ℓ&Vs&HH1&HH2).
      apply H2R.
      destruct (H1 ℓ) as (fid2&γ2&Hγ2); first by eapply elem_of_dom_2.
      do 3 eexists; repeat split; try done.
      eapply lookup_weaken in Hγ2 as Hγ2w; last done.
      rewrite -(H3 _ _ _ _ HH1 Hγ2w) in Hγ2; first done.
      right; by eexists.
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
  eapply map_disjoint_dom. eapply disjoint_weaken.
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
  induction σ as [|ℓ vv σ Hin IH] using map_ind; intros χMLold HχMLold .
  - exists χMLold, ∅, ∅; split_and!. 2: econstructor.
    + by eapply extended_to_refl.
    + intros γ; rewrite dom_empty_L; done.
    + split; rewrite dom_empty_L. 1: done.
      intros (fid & ℓ & Vs & H1 & H2). exfalso. rewrite lookup_empty in H2. done.
    + intros fid ℓ Vs γ blk Hc. exfalso. rewrite lookup_empty in Hc. done.
  - destruct (IH χMLold) as (χ0 & ζσ & ζi0 & Hext & Hstbl & Hstore). 1: done.
    destruct (ensure_in_χ_pub χ0 ℓ) as (χ1 & γ & fid & Hχ1 & Hγ & Hold); first by eapply extended_to_inj.
    apply extended_to_mono in Hχ1.
    destruct (deserialize_ML_block χ1 vv) as (χ2 & ζi2 & lvs & Hext2 & Helt); first by eapply extended_to_inj.
    edestruct (extended_to_trans) as (HextA&Hdisj1). 1: exact Hext. 1: eapply extended_to_trans; done.
    rewrite map_empty_union in Hdisj1.
    rewrite map_empty_union in HextA.
    assert (is_store_blocks χ2 (<[ℓ:=vv]> σ) (<[γ:=lvs]> ζσ)) as Hstore2.
    1: {eapply is_store_blocks_restore_loc.
        * eapply is_store_blocks_mono_weaken; first done. eapply extended_to_trans; done.
        * apply Hext2.
        * eapply lookup_weaken. 1: done. apply Hext2.
        * done. }
    assert (dom (<[γ:=lvs]> ζσ ∪ ζi0) ⊆ dom χ1) as Hsub3.
    { rewrite dom_union_L. eapply union_subseteq. split.
      * rewrite dom_insert_L. apply union_subseteq. split.
        1: eapply singleton_subseteq_l; first by eapply elem_of_dom_2.
        eapply elem_of_subseteq; intros k Hk.
        destruct Hstbl as (HH1&HH2). apply HH2 in Hk. destruct Hk as (?&?&?&H1&H2).
        eapply elem_of_dom_2. eapply lookup_weaken; first apply H1.
        eapply Hχ1.
      * etransitivity; last eapply subseteq_dom, Hχ1.
        eapply extended_to_dom_subset; done. }
    eexists χ2, (<[γ := lvs]> ζσ), (ζi0 ∪ ζi2). split_and!. 1-2:done.
    intros fid' ℓ' vs γ' blk H1 H2 H3.  destruct HextA as (HH1&HH2&HH3).
    apply lookup_union_Some in H3. 1: destruct H3 as [H3|H3].
    3: { eapply map_disjoint_dom; eapply elem_of_disjoint.
         intros x Hx1 Hx2; destruct (HH3 x Hx2) as (fid2&HH3'). destruct Hstore2 as [HHL HHR].
         apply HHR in Hx1. destruct Hx1 as (fid1 & l1 & Vs1 & ? & ?). by simplify_eq. }
    2: { edestruct HH3 as (fid2&HH3'). 2: erewrite HH3' in H2; simplify_eq. by eapply elem_of_dom_2. }
    apply lookup_insert_Some in H3. destruct H3 as [[? ?]|[Hne H3]].
    + subst. rewrite map_union_assoc.
      eapply lookup_weaken in Hγ. 2: eapply Hext2. rewrite Hγ in H2. injection H2; intros ->.
      rewrite lookup_insert in H1. injection H1; intros -> ->.
      by eapply is_heap_elt_weaken_2.
    + eapply lookup_insert_Some in H1. destruct H1 as [[-> H]|[Hne1 H1]].
      1: {exfalso. apply Hne. eapply HH1. 2: apply H2. 1: eapply lookup_weaken; first done. 1: apply Hext2. by (right; eexists). }
      assert (χ0 !! γ' = Some (LlocPublic fid' ℓ')) as H2'.
      1: {destruct Hstbl as [HHL HHR]. destruct (HHL ℓ') as (fid''&gg&Hgg); first by eapply elem_of_dom_2.
          assert (gg = γ') as ->.
          { eapply HH1. 2: done. 1: eapply lookup_weaken; first done.
            1: etransitivity; last eapply Hext2; eapply Hχ1. right; by eexists. }
          rewrite Hgg. eapply lookup_weaken in Hgg. 1: erewrite H2 in Hgg; by simplify_eq.
          etransitivity; last eapply Hext2; eapply Hχ1. }
      eapply is_heap_elt_weaken.
      1: eapply Hstore. 1: done. 3: etransitivity; first eapply Hχ1; last apply Hext2.
      2: erewrite lookup_union_l; first done. 1: done.
      1: eapply not_elem_of_dom; intros H; eapply Hext in H as (ffid&H'); congruence. 
      etransitivity; first eapply map_union_mono_l.
      2: etransitivity; first eapply map_union_mono_r. 4: done.
      1: eapply map_union_subseteq_l.
      1: eapply is_store_blocks_is_private_blocks_disjoint; done.
      eapply insert_subseteq, not_elem_of_dom.
      intros H. destruct Hstbl as [HHL HHR]. eapply HHR in H.
      destruct H as (?&?&?&Heq1&HeqF). eapply lookup_weaken in Heq1; first erewrite Hγ in Heq1. 2: apply Hχ1.
      injection Heq1; intros ->; rewrite HeqF in Hin; congruence. (*
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
      rewrite <- Hk1. f_equal. eapply Hχ1; try done. eapply lookup_weaken, Hχ1; done. *)
Qed.


Lemma deserialize_ML_heap_extra ζMLold χMLold σ : 
  lloc_map_inj χMLold
→ dom ζMLold ⊆ dom χMLold
→ pub_locs_in_lstore (χMLold) (ζMLold) = ∅ 
→ ∃ χC ζσ ζnewimm,
    extended_to χMLold ζnewimm χC
  ∧ is_store_blocks χC σ ζσ
  ∧ ζMLold ##ₘ (ζσ ∪ ζnewimm)
  ∧ is_store χC (ζMLold ∪ ζσ ∪ ζnewimm) σ.
Proof.
  intros H1 H2 H3.
  destruct (deserialize_ML_heap χMLold σ) as (χC&ζσ&ζi&HA1&HA2&HA3). 1: apply H1.
  assert (ζMLold ##ₘ ζσ ∪ ζi) as Hdisj.
  1: eapply map_disjoint_union_r; split; last (eapply map_disjoint_dom, disjoint_weaken; first apply HA1; done).
  1: { eapply map_disjoint_spec. intros γ b1 b2 HH1 HH2.
       destruct HA2 as [_ HA2R]. eapply elem_of_dom_2 in HH2. apply HA2R in HH2.
       destruct HH2 as (fid & ℓ & Vs & HH7 & HH8).
       unshelve epose proof (pub_locs_in_lstore_lookup _ _ γ fid ℓ _ _) as HH; last (erewrite H3 in HH; by apply lookup_empty_Some in HH).
       1: by eapply elem_of_dom_2.
       eapply elem_of_dom_2 in HH1.
       eapply elem_of_weaken in H2; last done.
       eapply elem_of_dom in H2; destruct H2 as [k Hk]. rewrite Hk. 
       eapply lookup_weaken in Hk; first erewrite HH7 in Hk. 2: eapply HA1. done. }
  do 3 eexists; split_and!; try done.
  - intros fid ℓ vs γ b He1 He2 He3.
    eapply is_heap_elt_weaken. 1: eapply HA3; try done. 2: done.
    + rewrite <- map_union_assoc in He3. eapply lookup_union_Some in He3; destruct He3; try done.
      destruct (HA2) as [HL HR]. destruct (HR γ) as [HRL HRR]. eapply elem_of_dom in HRR.
      2: do 3 eexists; done.
      destruct HRR as [vv Hvv].
      exfalso. erewrite map_disjoint_Some_r in H; try congruence. 1: done.
      erewrite lookup_union_Some_l; last done; first done.
    + erewrite <- map_union_assoc. eapply map_union_subseteq_r. done.
Qed.


End ChiZetaConstruction.

Section ThetaConstruction.

Lemma collect_dom_θ_vs (θdom : gset lloc) (vs : list lval) :
  exists θdom' : gset lloc,
    ∀ γ, Lloc γ ∈ vs ∨ γ ∈ θdom ↔ γ ∈ θdom'.
Proof.
  induction vs as [|[|ℓ] vs (θdom1 & IH)].
  - exists θdom. intros γ. split; last eauto. by intros [H%elem_of_nil|].
  - exists θdom1. intros γ. etransitivity; last by eapply IH.
    split; (intros [H|]; last by eauto); left.
    + apply elem_of_cons in H as [|]; done.
    + apply elem_of_cons; eauto.
  - exists (θdom1 ∪ {[ ℓ ]}). intros γ. split.
    + intros [[Hc|H]%elem_of_cons|?]; eapply elem_of_union.
      1: right; eapply elem_of_singleton; congruence.
      all: left; apply IH. 1: by left. by right.
    + intros [[H|H]%IH| ->%elem_of_singleton]%elem_of_union.
      1: left; by right. 1: by right.
      left; by left.
Qed.

Lemma collect_dom_θ_block (θdom : gset lloc) (blk : block) :
  exists θdom' : gset lloc,
    ∀ γ, lval_in_block blk (Lloc γ) ∨ γ ∈ θdom ↔ γ ∈ θdom'.
Proof.
  destruct blk as [[m [tg vs]]| |].
  { (* Bvblock *)
    destruct (collect_dom_θ_vs θdom vs) as (θdom' & H).
    exists θdom'. intros γ. split.
    - intros [HH|]; first inversion HH; subst; apply H; eauto.
    - intros [?|?]%H; eauto. left; by constructor. }
  { (* Bclosure *)
    exists θdom. intros γ. split; eauto. intros [H|]; auto.
    by inversion H. }
  { (* Bforeign *)
    exists θdom. intros γ. split; eauto. intros [H|]; auto.
    by inversion H. }
Qed.

Lemma collect_dom_θ_ζ_blocks (θdom : gset lloc) (ζ : lstore) :
  exists θdom' : gset lloc,
    forall γ, ((exists γ1 blk, ζ !! γ1 = Some blk ∧ lval_in_block blk (Lloc γ))
               ∨ γ ∈ θdom)
              ↔ γ ∈ θdom'.
Proof.
  induction ζ as [|k blk ζ Hne (θdom1 & Hdom1)] using map_ind.
  - exists θdom; split; auto. intros [(γ1&blk&H1&_)|]; auto.
    simplify_map_eq.
  - destruct (collect_dom_θ_block θdom1 blk) as (θdom2 & Hdom2).
    exists θdom2. intros γ; split.
    + intros [(γ1&blk'&[[-> ->]|[Hne2 Hin]]%lookup_insert_Some&H2)|Hold].
      { apply Hdom2; left; congruence. }
      { apply Hdom2. right. apply Hdom1. left. by do 2 eexists. }
      { apply Hdom2; right; apply Hdom1; right; done. }
    + intros [H|[(γ1&blk'&H1&H2)|H]%Hdom1]%Hdom2.
      1: left; do 2 eexists; split; first eapply lookup_insert; done.
      2: by right.
      left; do 2 eexists; split; last done; first rewrite lookup_insert_ne; first done.
      intros ->; rewrite Hne in H1; congruence.
Qed.

Lemma collect_dom_θ_ζ (θdom : gset lloc) (ζ : lstore) :
  exists θdom' : gset lloc,
    forall γ, (γ ∈ dom ζ ∨ (exists γ1 blk, ζ !! γ1 = Some blk ∧ lval_in_block blk (Lloc γ))
               ∨ γ ∈ θdom)
              ↔ γ ∈ θdom'.
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

End ThetaConstruction.

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
