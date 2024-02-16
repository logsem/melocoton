From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From transfinite.base_logic.lib Require Import ghost_map ghost_var gen_heap.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props stdpp_extra.
From melocoton.ml_lang Require Import lang primitive_laws.
From melocoton.interop Require Export basics basics_resources.

Section HGH.
Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!wrapperBasicsG Σ}.

(* TODO ?:
 - is_store_blocks -> is_store_blocks'
 - fusionner is_store_blocks' ∧ is_store en une seule definition commune
*)

Definition is_store_blocks' (χ : lloc_map) (σ : store) (ζ : lstore) :=
  (∀ ℓ, ℓ ∈ dom σ → ∃ γ, χ !! γ = Some (LlocPublic ℓ) ∧ γ ∈ dom ζ) ∧
  (∀ γ, γ ∈ dom ζ → ∀ ℓ, χ !! γ = Some (LlocPublic ℓ) → ℓ ∈ dom σ).

(* Definition lstore_representable (χ : lloc_map) (ζfull ζ : lstore) := *)
(*   ∃ σ, is_store_blocks' χ σ ζ ∧ is_store χ ζfull σ. *)
Definition lstore_representable (χ : lloc_map) (ζ : lstore) :=
  ∀ γ ℓ blk, χ !! γ = Some (LlocPublic ℓ) → ζ !! γ = Some blk →
    ∃ lvs, blk = Bvblock (Mut, (TagDefault, lvs)).

Local Ltac not_elem_of_dom :=
  repeat lazymatch goal with
  | H : _ !! _ = None |- _ => apply not_elem_of_dom in H
  | |- _ !! _ = None => apply not_elem_of_dom
  end; set_solver.

Definition lstore_hybrid_repr (χ : lloc_map) (ζfreeze : lstore) (σ : store) (ζ : lstore) :=
  ∃ ζσ,
    ζfreeze = ζσ ∪ ζ
  ∧ ζσ ##ₘ ζ
  ∧ is_store_blocks χ σ ζσ
  ∧ is_store χ ζfreeze σ.

Lemma lstore_hybrid_repr_refl χ ζ :
  lstore_hybrid_repr χ ζ ∅ ζ.
Proof using.
  exists ∅. split_and!.
  - rewrite left_id_L//.
  - map_disjoint_dom; set_solver.
  - split; set_solver.
  - intros ?. set_solver.
Qed.

Lemma lstore_hybrid_repr_lookup_loc χ ζfreeze σ ζ ℓ vs γ :
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lloc_map_inj χ →
  σ !! ℓ = Some vs →
  χ !! γ = Some (LlocPublic ℓ) →
  ∃ lvs, ζfreeze !! γ = Some (Bvblock (Mut, (TagDefault, lvs))) ∧
         Forall2 (is_val χ ζfreeze) vs lvs.
Proof using.
  intros (ζσ & Hfreezeeq & ? & Hstore_blocks & Hstore) Hχinj Hσ Hχ.
  edestruct is_store_blocks_has_loc as (ll & Hlχ & Hγζ);
    [apply Hstore_blocks|eapply elem_of_dom_2, Hσ|..].
  lloc_map_inj. apply elem_of_dom in Hγζ as [bb Hζσγ].
  assert (ζfreeze !! γ = Some bb) as Hfreezell.
  1: { rewrite Hfreezeeq. by apply lookup_union_Some_l. }
  unfold is_store in Hstore.
  specialize (Hstore ℓ vs γ bb Hσ Hχ Hfreezell) as Hstorel.
  inversion Hstorel; subst vs0 bb. eauto.
Qed.

Lemma block_sim_arr_of_auth' χ ζfreeze σ ζ vs lvs :
  lstore_hybrid_repr χ ζfreeze σ ζ →
  Forall2 (is_val χ ζfreeze) vs lvs →
  lloc_own_auth χ -∗
  lstore_own_auth ζ -∗
  lvs ~~∗ vs.
Proof using.
(*   intros (?&?&?&?&?) ?. eapply block_sim_arr_of_auth; eauto. *)
Admitted.

Lemma block_sim_arr_auth_is_val' χ ζfreeze σ ζ lvs vs :
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lloc_own_auth χ -∗
  lstore_own_auth ζ -∗
  lvs ~~∗ vs -∗
  ⌜Forall2 (is_val χ ζfreeze) vs lvs⌝.
Proof using.
(*   intros (?&->&?&?&?). iApply block_sim_arr_auth_is_val; eauto. *)
Admitted.

Lemma lstore_hybrid_repr_lookup_pub_lloc_notin χ ζfreeze σ ζ γ blk ℓ :
  lloc_map_inj χ →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  ζ !! γ = Some blk →
  χ !! γ = Some (LlocPublic ℓ) →
  σ !! ℓ = None.
Proof using.
  intros ? (ζσ&->&Hdisj&Hblks&Hstore) Hζ Hχ. apply not_elem_of_dom. intros Hℓ.
  apply Hblks in Hℓ as (?&?&?). lloc_map_inj. apply elem_of_dom_2 in Hζ.
  map_disjoint_dom. set_solver.
Qed.

Lemma lstore_hybrid_repr_lookup_loc_notin χ ζfreeze σ ζ γ ℓ vs :
  lloc_map_inj χ →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  σ !! ℓ = Some vs →
  χ !! γ = Some (LlocPublic ℓ) →
  ζ !! γ = None.
Proof using.
  intros ? (ζσ&->&?&Hblks&?) Hσ Hχ. apply elem_of_dom_2 in Hσ.
  apply Hblks in Hσ as (?&HH&?). lloc_map_inj.
  apply not_elem_of_dom. apply elem_of_dom_2 in HH.
  map_disjoint_dom. set_solver.
Qed.

Lemma lstore_hybrid_repr_lookup_lloc χ ζfreeze σ ζ γ blk :
  lstore_hybrid_repr χ ζfreeze σ ζ →
  ζ !! γ = Some blk →
  ζfreeze !! γ = Some blk.
Proof using. intros (ζσ&->&?&?&?) ?. by simplify_map_eq. Qed.

Lemma lstore_hybrid_repr_lstore_sub χ ζfreeze σ ζ :
  lstore_hybrid_repr χ ζfreeze σ ζ →
  ζ ⊆ ζfreeze.
Proof using. intros (ζσ&->&?&?&?). by eapply map_union_subseteq_r. Qed.

Lemma lstore_hybrid_repr_ml_to_mut χ ζfreeze σ ζ ℓ γ vs blk :
  lloc_map_inj χ →
  χ !! γ = Some (LlocPublic ℓ) →
  ζfreeze !! γ = Some blk →
  σ !! ℓ = Some vs →
  ζ !! γ = None →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lstore_hybrid_repr χ ζfreeze (delete ℓ σ) (<[γ:=blk]> ζ).
Proof using.
  intros Hχinj ? Hfγ ? ? (ζσ & -> & ? & ? & ?).
  exists (delete γ ζσ). split_and!.
  - symmetry. apply union_delete_insert.
    by apply lookup_union_Some_inv_l in Hfγ.
  - apply map_disjoint_insert_r_2. 1: apply lookup_delete.
    by apply map_disjoint_delete_l.
  - eapply is_store_blocks_delete_loc; eauto.
  - eapply is_store_discard_loc; eauto.
Qed.

Lemma lstore_hybrid_repr_ml_to_mut_many χ ζfreeze σ ζ σdel :
  lloc_map_inj χ →
  σdel ⊆ σ →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  ∃ ζadd, lstore_hybrid_repr χ ζfreeze (σ ∖ σdel) (ζ ∪ ζadd) ∧ ζ ##ₘ ζadd.
Proof using.
  intros Hχinj. induction σdel as [|ℓ vs σ' Hℓσ'] using map_ind.
  { intros _ HH. exists ∅. rewrite map_difference_empty right_id//.
    split; auto. eapply map_disjoint_empty_r. }
  { intros Hσ' HH. feed specialize IHσdel; eauto.
    { eapply insert_delete_subseteq in Hσ' as ->; eauto.
      eapply delete_subseteq. }
    destruct IHσdel as (ζadd & IH & IHdisj). clear HH.
    assert (Hℓ: ℓ ∈ dom (σ ∖ σ')).
    { rewrite dom_difference_L elem_of_difference. split.
      { rewrite map_subseteq_spec in Hσ'. eapply elem_of_dom. exists vs.
        eapply Hσ'. rewrite lookup_insert//. }
      { by apply not_elem_of_dom in Hℓσ'. } }
    pose proof Hℓ as Hℓ'. apply elem_of_dom in Hℓ' as (vs'&Hℓσ).
    assert (∃ γ, χ !! γ = Some (LlocPublic ℓ)) as (γ&Hγ).
    { destruct IH as (?&?&?&Hblk&?). eapply Hblk in Hℓ. naive_solver. }
    assert (Hγn: (ζ ∪ ζadd) !! γ = None)
      by (eapply lstore_hybrid_repr_lookup_loc_notin; eauto).
    assert (ζ !! γ = None) by (apply lookup_union_None in Hγn; naive_solver).
    pose proof Hℓσ as Hℓσ2.
    eapply lstore_hybrid_repr_lookup_loc in Hℓσ2 as (lvs&?&_); eauto.
    eapply (lstore_hybrid_repr_ml_to_mut _ _ _ _ ℓ) in IH; eauto; [].
    eexists (<[γ:=_]> ζadd). split.
    { rewrite -insert_union_r// -delete_difference//. }
    { eapply map_disjoint_insert_r; split; eauto. } }
Qed.

Lemma lstore_hybrid_repr_mut_to_ml χ ζfreeze σ ζ ℓ vs γ lvs :
  lloc_map_inj χ →
  χ !! γ = Some (LlocPublic ℓ) →
  σ !! ℓ = None →
  ζ !! γ = Some (Bvblock (Mut, (TagDefault, lvs))) →
  Forall2 (is_val χ ζfreeze) vs lvs →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lstore_hybrid_repr χ ζfreeze (<[ℓ:=vs]> σ) (delete γ ζ).
Proof using.
  intros ? ? ? ? ? (ζσ&->&?&?&?).
  exists (<[γ:=Bvblock (Mut, (TagDefault, lvs))]> ζσ). split_and!.
  - erewrite (union_insert_delete ζσ ζ). 2: eapply map_disjoint_Some_r. all: eauto.
  - apply map_disjoint_insert_l_2. 1: apply lookup_delete.
    by apply map_disjoint_delete_r.
  - eapply is_store_blocks_insert_loc; eauto.
  - eapply is_store_insert_loc; eauto. 1: eapply lookup_union_Some_r; eauto.
    by constructor.
Qed.

Lemma is_store_blocks'_empty_inv_r χ σ :
  is_store_blocks' χ σ ∅ →
  σ = ∅.
Proof using.
  intros [HH1 HH2].
  enough (¬ ∃ ℓ, ℓ ∈ dom σ) as HH by (eapply dom_empty_iff_L; set_solver).
  intros (ℓ & (?&?&?)%HH1). set_solver.
Qed.

Lemma is_store_blocks'_delete_loc χ σ ζ ℓ γ Vs :
  is_store_blocks' χ σ ζ →
  lloc_map_inj χ →
  χ !! γ = Some (LlocPublic ℓ) →
  σ !! ℓ = Some Vs →
  is_store_blocks' χ (delete ℓ σ) (delete γ ζ).
Proof.
  intros [Hs1 Hs2] χinj Hχℓ Hσℓ. split.
  { intros ℓ'. rewrite !dom_delete_L elem_of_difference not_elem_of_singleton.
    intros [Hℓ' ?]. apply Hs1 in Hℓ' as (γ'&?&?). eexists γ'. split; eauto.
    rewrite elem_of_difference not_elem_of_singleton. split; eauto.
    intros ->. simplify_map_eq. }
  { intros γ'. rewrite !dom_delete_L elem_of_difference not_elem_of_singleton.
    intros [Hγ' ?]. intros ℓ' Hχ. specialize (Hs2 γ' Hγ' ℓ' Hχ). set_solver. }
Qed.

Lemma is_store_blocks'_delete_nonpub_loc χ σ ζ γ :
  is_store_blocks' χ σ ζ →
  (χ !! γ = Some LlocPrivate ∨ χ !! γ = None) →
  is_store_blocks' χ σ (delete γ ζ).
Proof.
  intros [Hs1 Hs2] Hχℓ. split.
  { intros ℓ' Hℓ'. apply Hs1 in Hℓ' as (γ'&?&?). exists γ'. split; eauto.
    rewrite dom_delete_L. set_solver. }
  { intros γ'. rewrite !dom_delete_L elem_of_difference not_elem_of_singleton.
    intros [Hγ' ?]. intros ℓ' Hχ. specialize (Hs2 γ' Hγ' ℓ' Hχ). set_solver. }
Qed.

Lemma lstore_hybrid_repr_mut_to_ml_many χ ζfreeze σ ζ ζdel :
  lloc_map_inj χ →
  ζdel ⊆ ζ →
  dom ζdel ⊆ dom (lloc_map_pubs χ) →
  lstore_representable χ ζ →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  ∃ σadd, lstore_hybrid_repr χ ζfreeze (σ ∪ σadd) (ζ ∖ ζdel) ∧ is_store_blocks χ σadd ζdel.
Proof using.
  intros Hχinj. induction ζdel as [|γ blk ζ' Hγζ'] using map_ind.
  { intros _ _ ? HH. exists ∅. split.
    { rewrite map_difference_empty right_id//. }
    { split; set_solver. } }
  { intros Hζ' Hpubs Hrepr HH.
    (* facts about γ *)
    assert (ζ !! γ = Some blk).
    { rewrite map_subseteq_spec in Hζ'. eapply Hζ'. rewrite lookup_insert//. }
    assert (ζfreeze !! γ = Some blk) as Hζfreezeγ.
    { eapply lstore_hybrid_repr_lookup_lloc; eauto. }
    (* find ℓ related to γ in χ *)
    assert (∃ ℓ, χ !! γ = Some (LlocPublic ℓ)) as (ℓ&Hχℓ).
    { assert (γ ∈ dom (lloc_map_pubs χ)) as (ℓ&Hℓ)%elem_of_dom.
      { rewrite dom_insert_L in Hpubs. set_solver. }
      apply lloc_map_pubs_lookup_Some in Hℓ; eauto. }
    (* refine [blk] *)
    edestruct Hrepr as (lvs & Hblk); eauto; [].
    (* facts about ℓ *)
    (* assert (∃ vs, σadd !! ℓ = Some vs) as (vs&Hσℓ). *)
    (* { apply elem_of_dom. destruct Hblks as [_ HH2]. eapply HH2; eauto. set_solver. } *)
    assert (σ !! ℓ = None).
    { eapply lstore_hybrid_repr_lookup_pub_lloc_notin; eauto. }
    (* specialize the induction hypothesis and prove its requirements *)
    destruct IHζdel as (σadd & IH & Hdisj); eauto.
    { eapply insert_delete_subseteq in Hζ' as ->; eauto.
      eapply delete_subseteq. }
    { rewrite <- Hpubs. rewrite dom_insert_L. set_solver. }
    (* add the canonical representative of [lvs] to [σadd] *)
    exists (<[ℓ := map canon_val lvs]> σadd). split.
    2: { eapply is_store_blocks_insert_loc; eauto. }
    (* massage the goal before applying the unary [mut_to_ml] lemma *)
    rewrite -delete_difference -insert_union_r//.
    (* final step: unary mut_to_ml for γ<->ℓ *)
    eapply lstore_hybrid_repr_mut_to_ml; eauto.
    { eapply lookup_union_None. split; eauto.
      eapply lstore_hybrid_repr_lookup_pub_lloc_notin in IH; eauto.
      { apply lookup_union_None in IH; naive_solver. }
      { rewrite lookup_difference_Some; split; eauto. } }
    { rewrite lookup_difference_Some; split; subst; eauto. }
    { eapply canon_vals_is_val. } }
Qed.

Lemma lstore_hybrid_repr_expose_lloc χ ζfreeze σ ζ γ :
  lloc_map_inj χ →
  χ !! γ = Some LlocPrivate →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  ∃ ℓ, ℓ ∉ lloc_map_pub_locs χ ∧
       ℓ ∉ dom σ ∧
       lstore_hybrid_repr (<[γ:=LlocPublic ℓ]> χ) ζfreeze σ ζ.
Proof using.
  intros ? ? (ζσ&->&?&Hstore_blocks&?).
  pose (fresh_locs (lloc_map_pub_locs χ)) as ℓ. exists ℓ.
  assert (ℓ ∉ lloc_map_pub_locs χ).
  { intros Hℓ. apply (fresh_locs_fresh (lloc_map_pub_locs χ) 0 ltac:(lia)).
    rewrite /loc_add Z.add_0_r //. }
  assert (ℓ ∉ dom σ).
  { intros Hℓ. destruct Hstore_blocks as [HH1 _].
    destruct (HH1 _ Hℓ) as (γ'&Hγ'&?). by apply elem_of_lloc_map_pub_locs_1 in Hγ'. }
  split_and!; auto. exists ζσ. split_and!; eauto.
  - eapply is_store_blocks_expose_lloc; eauto.
  - eapply is_store_expose_lloc; eauto.
Qed.

Lemma lstore_hybrid_repr_freeze_block χ ζfreeze σ ζ γ bb :
  χ !! γ = Some LlocPrivate →
  ζ !! γ = Some (Bvblock (Mut, bb)) →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lstore_hybrid_repr χ (<[γ:=Bvblock (Immut, bb)]> ζfreeze) σ
    (<[γ:=Bvblock (Immut, bb)]> ζ).
Proof using.
  intros ? ? (ζσ&->&?&?&?). exists ζσ. split_and!; eauto.
  - rewrite insert_union_r. 1: done. eapply map_disjoint_Some_r; eauto.
  - apply map_disjoint_insert_r. split; last done. by eapply map_disjoint_Some_l.
  - eapply is_store_freeze_lloc; eauto.
    eapply lookup_union_Some_r; eauto.
Qed.

Lemma lstore_hybrid_repr_alloc_block χ ζfreeze σ ζ γ blk :
  χ !! γ = None →
  ζfreeze !! γ = None →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lstore_hybrid_repr (<[γ:=LlocPrivate]> χ) (<[γ:=blk]> ζfreeze) σ (<[γ:=blk]> ζ).
Proof using.
  intros ? Hζγ (ζσ&->&?&?&?). exists ζσ.
  apply lookup_union_None in Hζγ as [? ?].
  split_and!.
  - rewrite insert_union_r//.
  - apply map_disjoint_insert_r; split; auto.
  - eapply is_store_blocks_alloc_block; eauto.
  - eapply is_store_alloc_block; eauto. eapply lookup_union_None; eauto.
Qed.

Lemma lstore_hybrid_repr_modify_block χ ζfreeze σ ζ γ blk blk' :
  ζ !! γ = Some blk →
  mutability blk = Mut →
  lloc_map_inj χ →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lstore_hybrid_repr χ (<[γ:=blk']> ζfreeze) σ (<[γ:=blk']> ζ).
Proof.
  intros Hγ ? Hinj Hh.
  pose proof (lstore_hybrid_repr_lookup_lloc _ _ _ _ _ _ Hh Hγ) as Hγf.
  destruct Hh as (ζσ&->&Hdisj&Hstore_blocks&Hstore). exists ζσ. split_and!; eauto.
  - rewrite insert_union_r; first done. by erewrite map_disjoint_Some_l.
  - map_disjoint_dom. erewrite dom_insert_lookup; eauto.
  - eapply is_store_modify_priv_block; eauto. intros ℓ Vs Hχ Hσ.
    assert (γ ∉ dom ζσ) as Hnin.
    { apply elem_of_dom_2 in Hγ. apply map_disjoint_dom in Hdisj. set_solver. }
    destruct Hstore_blocks as [HH1 HH2].
    apply elem_of_dom_2 in Hσ. apply HH1 in Hσ as (γ'&?&?). by lloc_map_inj.
Qed.

Definition state_interp_with_safekeeping (σfull σ : store) : iProp Σ :=
  ∃ σsafe,
    "->" ∷ ⌜σfull = σ ∪ σsafe⌝ ∗
    "%SIWSdisj" ∷ ⌜σ ##ₘ σsafe⌝ ∗
    "SIWSfull" ∷ state_interp σfull ∗
    "SIWSsafe" ∷ ([∗ map] ℓ↦vs ∈ σsafe, ℓ ↦∗ vs).

Lemma siws_lookup (σfull σ : store) ℓ (vs : list val) :
  σ !! ℓ = Some vs →
  state_interp_with_safekeeping σfull σ -∗
  ⌜σfull !! ℓ = Some vs⌝.
Proof using.
  intros Hℓ. iNamed 1. iPureIntro.
  eapply lookup_union_Some; eauto.
Qed.

Lemma siws_valid σfull σ ℓ vs :
  state_interp_with_safekeeping σfull σ -∗
  ℓ ↦∗ vs -∗
  ⌜σ !! ℓ = Some vs⌝.
Proof using.
  iNamed 1. iIntros "Hpto".
  iDestruct (gen_heap_valid with "SIWSfull Hpto") as %Hℓ.
  apply lookup_union_Some in Hℓ as [Hℓ|Hℓ]; eauto.
  iDestruct (big_sepM_lookup with "SIWSsafe") as "Hpto'"; eauto.
  by iDestruct (gen_heap.mapsto_ne with "Hpto Hpto'") as %?.
Qed.

Lemma siws_delete σfull σ ℓ vs :
  state_interp_with_safekeeping σfull σ -∗
  ℓ ↦∗ vs -∗
  state_interp_with_safekeeping σfull (delete ℓ σ).
Proof using.
  iIntros "HS Hℓ". iDestruct (siws_valid with "HS Hℓ") as %Hℓ. iNamed "HS".
  iExists (<[ℓ:=vs]> σsafe). rewrite /named. iFrame. repeat iSplit; try iPureIntro.
  { rewrite union_delete_insert//. }
  { map_disjoint_dom. rewrite dom_delete_L dom_insert_L. set_solver. }
  { iApply big_sepM_insert; last by iFrame. apply map_disjoint_dom in SIWSdisj.
    apply not_elem_of_dom. apply elem_of_dom_2 in Hℓ. set_solver. }
Qed.

Lemma siws_restore (σfull σ : store) ℓ (vs : list val) :
  σ !! ℓ = None →
  σfull !! ℓ = Some vs →
  state_interp_with_safekeeping σfull σ -∗
  state_interp_with_safekeeping σfull (<[ℓ:=vs]> σ) ∗ ℓ ↦∗ vs.
Proof using.
  intros Hℓ Hfull. iNamed 1.
  eapply lookup_union_Some in Hfull as [Hfull|Hfull]; eauto; first congruence.
  iDestruct (big_sepM_delete with "SIWSsafe") as "[$ SIWSsafe]"; first done.
  iExists (delete ℓ σsafe). rewrite /named.
  iFrame. repeat iSplit; try iPureIntro; eauto.
  { rewrite union_insert_delete//. }
  { map_disjoint_dom. rewrite dom_insert_L dom_delete_L. set_solver. }
Qed.

Lemma siws_update_safe (σfull σ : store) ℓ (vs : list val) :
  σ !! ℓ = None →
  ℓ ∈ dom σfull →
  state_interp_with_safekeeping σfull σ ==∗
  state_interp_with_safekeeping (<[ℓ:=vs]> σfull) σ.
Proof using.
  intros Hℓ Hfull. iNamed 1.
  rewrite dom_union_L elem_of_union in Hfull.
  destruct Hfull as [Hfull|Hfull]; first by eapply not_elem_of_dom in Hℓ.
  apply elem_of_dom in Hfull as [vs' Hfull].
  iDestruct (big_sepM_delete with "SIWSsafe") as "[Hℓ SIWSsafe]"; first by eauto.
  iMod (gen_heap_update with "SIWSfull Hℓ") as "[SIWSfull Hℓ]". iModIntro.
  iDestruct (big_sepM_insert _ _ _ vs with "[$SIWSsafe $Hℓ]") as "SIWSsafe".
  1: by rewrite lookup_delete. rewrite insert_delete_insert.
  iExists (<[ℓ:=vs]> σsafe). rewrite /named. iFrame. iPureIntro; split_and!.
  { rewrite insert_union_r//. }
  { map_disjoint_dom. rewrite dom_insert_L. apply elem_of_dom_2 in Hfull.
    set_solver. }
Qed.

Lemma siws_alloc_safe (σfull σ : store) ℓ (vs : list val) :
  σfull !! ℓ = None →
  state_interp_with_safekeeping σfull σ ==∗
  state_interp_with_safekeeping (<[ℓ := vs]> σfull) σ.
Proof using.
  intros Hℓ. iNamed 1.
  iMod (gen_heap_alloc with "SIWSfull") as "(SIWSfull & Hℓ & _)"; first done.
  eapply lookup_union_None in Hℓ as [? ?].
  iDestruct (big_sepM_insert with "[$SIWSsafe $Hℓ]") as "SIWSsafe"; first done.
  iModIntro. rewrite /state_interp_with_safekeeping /named.
  iExists _. iFrame. iPureIntro; split_and!.
  { rewrite insert_union_r//. }
  { apply map_disjoint_insert_r_2; eauto. }
Qed.

Lemma siws_alloc_safe_as_needed (σfull σ : store) (target : gset loc) :
  dom σfull ⊆ target →
  state_interp_with_safekeeping σfull σ ==∗
  ∃ σfull', state_interp_with_safekeeping σfull' σ ∗
    ⌜dom σfull' = target⌝ ∗ ⌜σfull ⊆ σfull'⌝.
Proof using.
  pose (missing := target ∖ dom σfull). intros Htarget.
  assert (Hdisj: missing ## dom σfull) by set_solver.
  assert (Htgt: target = dom σfull ∪ missing); first by eapply union_difference_L.
  clearbody missing. subst target.
  induction missing as [| ℓ missing Hℓmis IH] using set_ind_L.
  { iIntros "H !>". iExists σfull; repeat iSplit; eauto. rewrite right_id_L//. }
  { feed specialize IH; [set_solver..|]. iIntros "H".
    iMod (IH with "H") as (σfull') "(H & %Hdom & %Hsub)".
    assert (σfull' !! ℓ = None) by (apply not_elem_of_dom; set_solver).
    iMod (siws_alloc_safe _ _ ℓ [] with "H") as "H"; first done.
    iModIntro. iExists _. iFrame. iPureIntro; split_and!; eauto.
    { rewrite dom_insert_L. set_solver. }
    { rewrite -> Hsub. eapply insert_subseteq; eauto. } }
Qed.

Definition HGH (χ : lloc_map) (σo : option store) (ζ : lstore) : iProp Σ :=
  ∃ (ζg : lstore) (χg : lloc_map),
  "HGHζ" ∷ lstore_own_auth ζg ∗
  "HGHχ" ∷ lloc_own_auth χg ∗
  "HGHσo" ∷ match σo with
  | None => ∃ σsafe,
    "[-> ->]" ∷ ⌜ζg = ζ ∧ χg = χ⌝ ∗
    "HGHσsafe" ∷ ([∗ map] ℓ↦vs ∈ σsafe, ℓ ↦∗ vs) ∗
     "%HGHpub" ∷ ⌜pub_locs_in_lstore χ ζ = ∅⌝
    (* "%HGHσsafe" ∷ ⌜codom (pub_locs_in_lstore χg ζg) ⊆ dom σsafe⌝ *)
  | Some σ => ∃ ζfreeze σfull,
    "HGHσ" ∷ state_interp_with_safekeeping σfull σ ∗
    "%HGHζfreeze" ∷ ⌜freeze_lstore ζ ζfreeze⌝ ∗
    "%HGHζrepr" ∷ ⌜lstore_hybrid_repr χg ζfreeze σ ζg⌝ ∗
    "%HGHσfull" ∷ ⌜dom σfull = lloc_map_pub_locs χg⌝
  end ∗
  "%HGHζgrepr" ∷ ⌜lstore_representable χg ζg⌝ ∗
  "%Hχexp" ∷ ⌜expose_llocs χ χg⌝ ∗
  "%Hother_blocks" ∷ ⌜dom ζ ⊆ dom χ⌝.

Lemma hgh_dom_lstore_sub χ σo ζ : HGH χ σo ζ -∗ ⌜dom ζ ⊆ dom χ⌝.
Proof using. iNamed 1. eauto. Qed.

Lemma hgh_χ_inj χ ζ : HGH χ None ζ -∗ ⌜lloc_map_inj χ⌝.
Proof using. iNamed 1. iNamed "HGHσo". iPureIntro. apply Hχexp. Qed.

Lemma hgh_None_pub_locs_in_lstore χ ζ :
  HGH χ None ζ -∗ ⌜pub_locs_in_lstore χ ζ = ∅⌝.
Proof using. iNamed 1. by iNamed "HGHσo". Qed.

Lemma hgh_pointsto_has_lloc χ σ ζ ℓ vs :
  HGH χ (Some σ) ζ -∗
  ℓ ↦∗ vs -∗
  ∃ γ, γ ~ℓ~ ℓ.
Proof using.
  iIntros "H Hpto". iNamed "H". iNamed "HGHσo".
  iDestruct (siws_valid with "HGHσ Hpto") as %Hℓ.
  destruct HGHζrepr as (? & ? & ? & ? & ?).
  edestruct is_store_blocks_has_loc as (γ & Hχγ & Hγ); eauto;
    first by eapply elem_of_dom_2.
  iExists γ. by iApply lloc_own_auth_get_pub.
Qed.

Lemma hgh_block_sim_is_val χ ζ vs lvs :
  HGH χ None ζ -∗
  lvs ~~∗ vs -∗
  ⌜Forall2 (is_val χ ζ) vs lvs⌝.
Proof using.
  iNamed 1. iIntros "Hsim". iNamed "HGHσo".
  (* iDestruct (block_sim_arr_auth_is_val' with "HGHχ HGHζ Hsim") as %?; eauto. *)
  (* apply lstore_hybrid_repr_refl. *)
Admitted.

Lemma hgh_block_sim_of χ ζ σ vs lvs :
  Forall2 (is_val χ ζ) vs lvs →
  HGH χ (Some σ) ζ -∗
  lvs ~~∗ vs.
Proof using.
  intros Hvs. iNamed 1. iNamed "HGHσo".
  (* iApply (block_sim_arr_of_auth' with "HGHχ HGHζ"); eauto. *)
  (* eapply Forall2_impl; first done. intros ? ? ?. *)
  (* eapply is_val_freeze; eauto. eapply is_val_expose_llocs; eauto. *)
Admitted.

(* Local Lemma interp_ML_discarded_locs_pub χpub (σ:store) : *)
(*     gen_heap_interp σ *)
(*  -∗ ([∗ map] ℓ ∈ χpub, ℓ ↦M/) *)
(*  -∗ ⌜map_Forall (λ (_ : nat) (ℓ : loc), σ !! ℓ = Some None) χpub⌝. *)
(* Proof using. *)
(*   induction χpub as [|k l χpub Hin IH] using map_ind; iIntros "HH HK". *)
(*   - iPureIntro. apply map_Forall_empty. *)
(*   - iPoseProof (big_sepM_insert) as "[HL _]". 1: apply Hin. *)
(*     iPoseProof ("HL" with "HK") as "[H1 H2]". *)
(*     iPoseProof (IH with "HH H2") as "%HIH". *)
(*     iPoseProof (gen_heap_valid with "HH H1") as "%Hv". *)
(*     iPureIntro. apply map_Forall_insert. 1: done. split; done. *)
(* Qed. *)

(* Lemma hgh_discarded_locs_pub χ σ ζ : *)
(*   HGH χ None ζ -∗ *)
(*   state_interp σ -∗ *)
(*   ⌜map_Forall (λ (_ : nat) (ℓ : loc), σ !! ℓ = Some None) (pub_locs_in_lstore χ ζ)⌝. *)
(* Proof using. *)
(*   iNamed 1. iNamed "HGHσo". iIntros "Hσ". *)
(*   by iApply (interp_ML_discarded_locs_pub with "Hσ HGHχNone"). *)
(* Qed. *)

Lemma lstore_representable_empty : lstore_representable ∅ ∅.
Proof. intros ? ? ?. naive_solver. Qed.

Lemma hgh_empty :
  lstore_own_auth ∅ -∗
  lloc_own_auth ∅ -∗
  HGH ∅ None ∅.
Proof using.
  iIntros "Hζ Hχ". rewrite /HGH /named. iExists ∅, ∅.
  iFrame. iSplit.
  { iExists ∅. (* rewrite pub_locs_in_lstore_empty big_sepM_empty. *)
    rewrite big_sepM_empty.
    iPureIntro; split_and!; eauto. (* set_solver. *) }
  { iPureIntro; split_and!; eauto.
    - apply lstore_representable_empty.
    - by apply expose_llocs_refl.
    - set_solver. }
Qed.

Lemma lstore_hybrid_repr_lookup_lloc_notin χ ζfreeze σ ζ γ blk ℓ :
  lloc_map_inj χ →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  ζ !! γ = Some blk →
  χ !! γ = Some (LlocPublic ℓ) →
  σ !! ℓ = None.
Proof using.
  intros Hinj (ζσ&->&Hdisj&Hblk&Hstore) Hζ Hχ.
  destruct (σ !! ℓ) eqn:Hℓ; eauto. apply elem_of_dom_2 in Hℓ.
  destruct Hblk as [Hsl Hsr]. apply Hsl in Hℓ as (γ'&?&?). lloc_map_inj.
  map_disjoint_dom. apply elem_of_dom_2 in Hζ. set_solver.
Qed.

Lemma is_store_blocks'_insert_loc χ σ ζ ℓ γ Vs blk:
  is_store_blocks' χ σ ζ →
  lloc_map_inj χ →
  χ !! γ = Some (LlocPublic ℓ) →
  is_store_blocks' χ (<[ℓ:=Vs]> σ) (<[γ:=blk]> ζ).
Proof.
  intros [Hsl Hsr] Hχinj Hχℓ. split.
  { intros ℓ'. rewrite !dom_insert_L elem_of_union elem_of_singleton. intros [->|Hℓ'].
    { eexists. split; eauto. rewrite elem_of_union elem_of_singleton. eauto. }
    { apply Hsl in Hℓ' as (γ'&?&?). exists γ'. split; eauto.
      rewrite elem_of_union elem_of_singleton. eauto. } }
  { intros γ'. rewrite !dom_insert_L elem_of_union elem_of_singleton. intros [->|Hγ'].
    { intros ℓ' Hℓ'. simplify_map_eq. set_solver. }
    { intros ℓ' Hℓ'. set_solver. } }
Qed.

Lemma is_store_blocks'_insert_nonpub_loc χ σ ζ γ blk:
  is_store_blocks' χ σ ζ →
  (χ !! γ = None ∨ χ !! γ = Some LlocPrivate) →
  is_store_blocks' χ σ (<[γ:=blk]> ζ).
Proof.
  intros [Hsl Hsr] ?. split.
  { intros ℓ' Hℓ'. apply Hsl in Hℓ' as (γ'&?&?). exists γ'. split; eauto.
    set_solver. }
  { intros γ' Hγ' ℓ Hχ. eapply Hsr; eauto.
    rewrite dom_insert_L elem_of_union elem_of_singleton in Hγ'. naive_solver. }
Qed.

(* Lemma lstore_representable_insert χ ζfull ζ γ lvs ℓ vs (σ: store) : *)
(*   lloc_map_inj χ → *)
(*   χ !! γ = Some (LlocPublic ℓ) → *)
(*   ζ !! γ = None → *)
(*   ζfull !! γ = Some (Bvblock (Mut, (TagDefault, lvs))) → *)
(*   σ !! ℓ = Some vs → *)
(*   Forall2 (is_val χ ζfull) vs lvs → *)
(*   lstore_representable χ ζfull ζ → *)
(*   lstore_representable χ ζfull (<[γ:=Bvblock (Mut, (TagDefault, lvs))]> ζ). *)
(* Proof using. *)
(*   intros ? ? ? ? ? ? (σrepr&Hblks&Hstore). *)
(*   exists (<[ℓ:=vs]> σrepr). split. *)
(*   { eapply is_store_blocks'_insert_loc; eauto. } *)
(*   { eapply is_store_insert_loc; eauto. econstructor; eauto. } *)
(* Qed. *)

Lemma lstore_representable_insert χ ζ γ lvs :
  lstore_representable χ ζ →
  lstore_representable χ (<[γ:=Bvblock (Mut, (TagDefault, lvs))]> ζ).
Proof using.
  intros ? γ' ℓ blk ? ?%lookup_insert_Some. naive_solver.
Qed.

Lemma hgh_ml_to_mut χ σ ζ ℓ γ vs :
  HGH χ (Some σ) ζ -∗
  ℓ ↦∗ vs -∗
  γ ~ℓ~ ℓ ==∗
  ∃ lvs,
    HGH χ (Some (delete ℓ σ)) ζ ∗
    lstore_own_elem γ (DfracOwn 1) (Bvblock (Mut, (TagDefault, lvs))) ∗
    lvs ~~∗ vs.
Proof using.
  iIntros "H Hℓ #Hsim". iNamed "H". iNamed "HGHσo".
  iDestruct (siws_valid with "HGHσ Hℓ") as %Hσℓ.
  iDestruct (lloc_own_pub_of with "HGHχ Hsim") as %Hχγ.
  assert (ζg !! γ = None) as Hζγ.
  { eapply lstore_hybrid_repr_lookup_loc_notin; eauto. }
  edestruct lstore_hybrid_repr_lookup_loc as (lvs & Hζfγ & Hlvs); eauto; [].
  iAssert (lvs ~~∗ vs) as "#Hblock".
  1: by iApply (block_sim_arr_of_auth' with "HGHχ HGHζ").
  iDestruct (siws_delete with "HGHσ Hℓ") as "HGHσ".
  iMod (lstore_own_insert _ γ (Bvblock (Mut, _)) with "HGHζ") as "(HGHζ & Hz)";
    first done.
  iModIntro. iExists lvs. iFrame "Hblock Hz".
  rewrite /HGH /named. iExists _, _. iFrame "HGHχ HGHζ". iSplitL "HGHσ".
  { iExists _, _. iFrame. iPureIntro. split_and!; eauto.
    { eapply lstore_hybrid_repr_ml_to_mut; eauto. } }
  iSplit; eauto. iPureIntro. eapply lstore_representable_insert; eauto.
Qed.

Set Nested Proofs Allowed.

(* Lemma lstore_representable_delete χ ζfull ζ γ : *)
(*   lloc_map_inj χ → *)
(*   lstore_representable χ ζfull ζ → *)
(*   lstore_representable χ ζfull (delete γ ζ). *)
(* Proof using. *)
(*   intros ? HH. *)
(*   destruct (decide (γ ∈ dom ζ)) as [Hin|Hnin]. *)
(*   { destruct HH as (σrepr&Hblks&Hstore). *)
(*     destruct (χ !! γ) as [[ℓ|]|] eqn:Hχ. *)
(*     { eapply Hblks in Hin; eauto. exists (delete ℓ σrepr). *)
(*       apply elem_of_dom in Hin as (?&?). split. *)
(*       { eapply is_store_blocks'_delete_loc; eauto. } *)
(*       { by eapply is_store_discard_loc. } } *)
(*     all: exists σrepr; split; eauto. *)
(*     all: eapply is_store_blocks'_delete_nonpub_loc; eauto. } *)
(*   { rewrite delete_notin//. by eapply not_elem_of_dom. } *)
(* Qed. *)

Lemma lstore_representable_delete χ ζ γ :
  lstore_representable χ ζ →
  lstore_representable χ (delete γ ζ).
Proof using.
  intros ? ? ? ? ? ?%lookup_delete_Some. naive_solver.
Qed.

Lemma hgh_mut_to_ml χ σ ζ ℓ γ lvs vs :
  HGH χ (Some σ) ζ -∗
  lstore_own_elem γ (DfracOwn 1) (Bvblock (Mut, (TagDefault, lvs))) -∗
  γ ~ℓ~ ℓ -∗
  lvs ~~∗ vs
  ==∗
  HGH χ (Some (<[ℓ:=vs]> σ)) ζ ∗
  ℓ ↦∗ vs.
Proof using.
  iIntros "H Hγ #Hsim #Hblksim". iNamed "H". iNamed "HGHσo".
  iDestruct (lloc_own_pub_of with "HGHχ Hsim") as %Hγℓ.
  iDestruct (lstore_own_elem_of with "HGHζ Hγ") as %Hζγ.
  assert (σ !! ℓ = None) as Hσℓ.
  { eapply lstore_hybrid_repr_lookup_lloc_notin; eauto. }
  iDestruct (block_sim_arr_auth_is_val' with "HGHχ HGHζ Hblksim") as %Hsim;
    try done; [].
  iMod (siws_update_safe _ _ ℓ vs with "HGHσ") as "HGHσ"; eauto.
  { rewrite HGHσfull. eapply elem_of_lloc_map_pub_locs_1; eauto. }
  iDestruct (siws_restore _ _ ℓ vs with "HGHσ") as "[HGHσ Hℓ]"; auto.
  { rewrite lookup_insert//. }
  iDestruct (lstore_own_elem_to_mut with "Hγ") as "Hγ"; first done.
  iMod (lstore_own_delete with "HGHζ Hγ") as "HGHζ".
  iModIntro. iFrame "Hℓ". rewrite /HGH /named.
  iExists _, _. iFrame. iSplit.
  { iExists _, _. iFrame. iPureIntro; split_and!; eauto.
    { eapply lstore_hybrid_repr_mut_to_ml; eauto. }
    { rewrite dom_insert_L HGHσfull. eapply subseteq_union_1_L.
      rewrite singleton_subseteq_l.
      eapply elem_of_lloc_map_pub_locs_1; eauto. } }
  { iPureIntro; split_and!; eauto. eapply lstore_representable_delete; eauto. }
Qed.

Lemma is_store_blocks'_expose_lloc χ ζ σ ℓ γ vs :
  is_store_blocks' χ σ ζ →
  χ !! γ = Some LlocPrivate →
  γ ∈ dom ζ →
  ℓ ∉ dom σ →
  is_store_blocks' (<[γ:=LlocPublic ℓ]> χ) (<[ℓ:=vs]> σ) ζ.
Proof.
  intros [Hsl Hsr] Hγ ? Hℓdom. split.
  { intros ℓ'. rewrite dom_insert_L elem_of_union elem_of_singleton. intros [->|Hℓ'].
    { exists γ. rewrite lookup_insert. split; eauto. }
    { apply Hsl in Hℓ' as (γ'&?&?). exists γ'.
      rewrite lookup_insert_ne//. congruence. } }
  { intros γ' Hγ' ℓ' [[-> ?]|[? ?]]%lookup_insert_Some; simplify_map_eq.
    { set_solver. }
    { rewrite dom_insert_L elem_of_union. right. eapply Hsr; eauto. } }
Qed.

(* Lemma lstore_representable_expose_lloc χ ζfull ζ γ ℓ lvs : *)
(*   lloc_map_inj χ → *)
(*   χ !! γ = Some LlocPrivate → *)
(*   ζ !! γ = Some (Bvblock (Mut, (TagDefault, lvs))) → *)
(*   ζfull !! γ = Some (Bvblock (Mut, (TagDefault, lvs))) → *)
(*   ℓ ∉ lloc_map_pub_locs χ → *)
(*   lstore_representable χ ζfull ζ → *)
(*   lstore_representable (<[γ:=LlocPublic ℓ]> χ) ζfull ζ. *)
(* Proof using. *)
(*   intros ? ? ? ? Hℓ (σrepr&Hblks&Hstore). *)
(*   exists (<[ℓ := map canon_val lvs]> σrepr). *)
(*   assert (ℓ ∉ dom σrepr). *)
(*   { intros (γ'&?&?)%Hblks. apply Hℓ, elem_of_lloc_map_pub_locs. eauto. } *)
(*   split. *)
(*   { eapply is_store_blocks'_expose_lloc; eauto. by eapply elem_of_dom_2. } *)
(*   { eapply (is_store_expose_lloc _ _ _ ℓ γ) in Hstore; eauto. *)
(*     eapply is_store_insert_loc; eauto. *)
(*     { by eapply lloc_map_inj_insert_pub. } *)
(*     { rewrite lookup_insert//. } *)
(*     { econstructor. eapply canon_vals_is_val. } } *)
(* Qed. *)

Lemma lstore_representable_expose_lloc χ ζ γ ℓ lvs :
  ζ !! γ = Some (Bvblock (Mut, (TagDefault, lvs))) →
  lstore_representable χ ζ →
  lstore_representable (<[γ:=LlocPublic ℓ]> χ) ζ.
Proof using.
  intros ? ? ? ? ? ?%lookup_insert_Some. naive_solver.
Qed.

(* ownership over the points-to is required to attest that the block being
   exposed is indeed a block that can be exposed (following [is_heap_elt]), i.e.
   of the form [Mut (TagDefault, ..)]. *)
Lemma hgh_expose_lloc χ σ ζ γ lvs :
  HGH χ (Some σ) ζ -∗
  lstore_own_elem γ (DfracOwn 1) (Bvblock (Mut, (TagDefault, lvs))) -∗
  γ ~ℓ~/
  ==∗
  ∃ ℓ, ⌜ℓ ∉ dom σ⌝ ∗
    HGH χ (Some σ) ζ ∗
    lstore_own_elem γ (DfracOwn 1) (Bvblock (Mut, (TagDefault, lvs))) ∗
    γ ~ℓ~ ℓ.
Proof using.
  iIntros "H Hγ Hpriv". iNamed "H". iNamed "HGHσo".
  iDestruct (lloc_own_priv_of with "HGHχ Hpriv") as %Hχγ.
  iDestruct (lstore_own_elem_of with "HGHζ Hγ") as %Hζγ.
  edestruct lstore_hybrid_repr_expose_lloc as (ℓ & Hℓ & Hℓσ & Hrepr); eauto; [].
  assert (Hℓσfull: ℓ ∉ dom σfull) by rewrite HGHσfull//.
  iMod (siws_alloc_safe _ _ _ [] with "HGHσ") as "HGHσ"; first by eapply not_elem_of_dom.
  iMod (lloc_own_expose with "HGHχ Hpriv") as "[HGHχ Hpriv]"; first done.
  iModIntro. iExists ℓ. iSplit; first done. iFrame "Hpriv Hγ". rewrite /HGH /named.
  iExists _, _. iFrame. iSplit.
  { iExists _, _. iFrame. iPureIntro; split_and!; eauto.
    { rewrite dom_insert_L HGHσfull lloc_map_pub_locs_insert_pub//. naive_solver. } }
  { iPureIntro; split_and!; eauto.
    { eapply lstore_representable_expose_lloc; eauto. }
    { eapply expose_llocs_trans; first done. eapply expose_llocs_insert; eauto. } }
Qed.

(* Lemma lstore_representable_freeze_block χ ζfull ζ γ blk blk' bb : *)
(*   ζ !! γ = Some blk → *)
(*   ζfull !! γ = Some (Bvblock (Mut, bb)) → *)
(*   χ !! γ = Some LlocPrivate → *)
(*   lstore_representable χ ζfull ζ → *)
(*   lstore_representable χ (<[γ:=Bvblock (Immut, bb)]> ζfull) (<[γ:=blk']> ζ). *)
(* Proof using. *)
(*   intros ? ? ? (σrepr&Hblks&Hstore). exists σrepr. split. *)
(*   { eapply is_store_blocks'_insert_nonpub_loc; eauto. } *)
(*   { eapply is_store_freeze_lloc; eauto. } *)
(* Qed. *)

Lemma lstore_representable_freeze_block χ ζ γ bb :
  χ !! γ = Some LlocPrivate →
  lstore_representable χ ζ →
  lstore_representable χ (<[γ:=Bvblock (Immut, bb)]> ζ).
Proof using.
  intros ? ? ? ? ? ? ?%lookup_insert_Some. naive_solver.
Qed.

Lemma hgh_freeze_block χ σ ζ γ bb :
  HGH χ (Some σ) ζ -∗
  lstore_own_elem γ (DfracOwn 1) (Bvblock (Mut, bb)) -∗
  γ ~ℓ~/
  ==∗
  HGH χ (Some σ) ζ ∗
  lstore_own_elem γ (DfracOwn 1) (Bvblock (Immut, bb)) ∗
  γ ~ℓ~/.
Proof using.
  iIntros "H Hγ Hfresh". iNamed "H". iNamed "HGHσo".
  iDestruct (lstore_own_elem_of with "HGHζ Hγ") as %?.
  iDestruct (lloc_own_priv_of with "HGHχ Hfresh") as %?.
  iDestruct (lstore_own_elem_to_mut with "Hγ") as "Hγ"; first done.
  iMod (lstore_own_update _ _ _ (Bvblock (Immut, bb)) with "HGHζ Hγ") as "(HGHζ & Hγ)".
  iModIntro. iFrame "Hγ Hfresh". rewrite /HGH /named. iExists _, _. iFrame. iSplit.
  { iExists (<[γ:=Bvblock (Immut, bb)]> ζfreeze), _. iFrame.
    iPureIntro; split_and!; eauto.
    { eapply freeze_lstore_freeze_lloc; eauto.
      by eapply lstore_hybrid_repr_lookup_lloc. }
    { eapply lstore_hybrid_repr_freeze_block; eauto. } }
  { iPureIntro; split_and!; eauto. eapply lstore_representable_freeze_block; eauto. }
Qed.

Lemma is_store_blocks'_alloc_block χ σ ζ γ blk :
  χ !! γ = None →
  is_store_blocks' χ σ ζ →
  is_store_blocks' (<[γ:=LlocPrivate]> χ) σ (<[γ:=blk]> ζ).
Proof.
  intros ? [Hsl Hsr]. split.
  { intros ℓ (γ'&?&?)%Hsl. exists γ'. rewrite lookup_insert_ne. 2: naive_solver.
    split; eauto. set_solver. }
  { intros γ'. rewrite dom_insert_L elem_of_union elem_of_singleton. intros [->|Hγ'].
    { intros ℓ. rewrite lookup_insert. naive_solver. }
    { intros ℓ. intros ?%lookup_insert_Some. naive_solver. } }
Qed.

(* Lemma lstore_representable_alloc_block χ ζfull ζ γ blk : *)
(*   χ !! γ = None → *)
(*   ζfull !! γ = None → *)
(*   lstore_representable χ ζfull ζ → *)
(*   lstore_representable (<[γ:=LlocPrivate]> χ) (<[γ:=blk]> ζfull) (<[γ:=blk]> ζ). *)
(* Proof. *)
(*   intros ? ? (σrepr&Hblk&Hstore). exists σrepr. split. *)
(*   { eapply is_store_blocks'_alloc_block; eauto. } *)
(*   { eapply is_store_alloc_block; eauto. } *)
(* Qed. *)

Lemma lstore_representable_alloc_block χ ζ γ blk :
  lstore_representable χ ζ →
  lstore_representable (<[γ:=LlocPrivate]> χ) (<[γ:=blk]> ζ).
Proof using.
  intros ? ? ? ? ?%lookup_insert_Some ?%lookup_insert_Some. naive_solver.
Qed.

Lemma hgh_alloc_block χ σ ζ γ blk :
  χ !! γ = None →
  HGH χ (Some σ) ζ ==∗
  HGH (<[γ := LlocPrivate]> χ) (Some σ) (<[γ := blk]> ζ) ∗
  lstore_own_elem γ (DfracOwn 1) blk ∗
  γ ~ℓ~/.
Proof using.
  intros Hχγ. iNamed 1. iNamed "HGHσo". pose proof Hχexp as [? _].
  assert (dom ζg ⊆ dom χ).
  { rewrite <-Hother_blocks. destruct HGHζfreeze as [-> _].
    destruct HGHζrepr as (?&->&_&_&_). set_solver. }
  iMod (lstore_own_insert _ γ blk with "HGHζ") as "(HGHζ & Hb)".
  1: by not_elem_of_dom.
  assert (Hχg: χg !! γ = None) by not_elem_of_dom.
  iMod (lloc_own_insert_priv _ γ with "HGHχ") as "(HGHχ&Hpriv)"; first done.
  iModIntro. iFrame "Hpriv Hb". rewrite /HGH /named.
  iExists _, _. iFrame. iSplit.
  { iExists (<[γ := blk]> ζfreeze), _. iFrame. iPureIntro; split_and!; eauto.
    { by eapply freeze_lstore_insert. }
    { eapply lstore_hybrid_repr_alloc_block; eauto.
      destruct HGHζfreeze as [? _]. not_elem_of_dom. }
    { rewrite HGHσfull lloc_map_pub_locs_insert_priv//. } }
  { iPureIntro; split_and!.
    { eapply lstore_representable_alloc_block; eauto. }
      (* apply not_elem_of_dom. intros Hγ. rewrite elem_of_subseteq in Hother_blocks. *)
      (* rewrite -(proj1 HGHζfreeze) in Hγ. *)
      (* by apply Hother_blocks, not_elem_of_dom in Hγ. } } *)
    { eapply expose_llocs_insert_both; eauto. }
    { set_solver. } }
Qed.

Lemma hgh_lookup_block χ σo ζ γ dq b :
  HGH χ σo ζ -∗
  lstore_own_elem γ dq b -∗
  ⌜∃ b', freeze_block b' b ∧ ζ !! γ = Some b'⌝.
Proof using.
  iNamed 1. iIntros "Hγ".
  iDestruct (lstore_own_elem_of with "HGHζ Hγ") as %Hγ.
  destruct σo as [σ|]; iNamed "HGHσo"; last by eauto.
  destruct HGHζfreeze as [H1 H2].
  eapply lstore_hybrid_repr_lookup_lloc in Hγ; last eassumption.
  enough (is_Some (ζ !! γ)) as [b' Hb']; first by eauto.
  apply elem_of_dom. apply elem_of_dom_2 in Hγ. set_solver.
Qed.

Lemma hgh_lookup_vblock χ σo ζ γ dq m bb :
  HGH χ σo ζ -∗
  lstore_own_elem γ dq (Bvblock (m, bb)) -∗
  ⌜∃ m', (m' = Immut → m = Immut) ∧ ζ !! γ = Some (Bvblock (m', bb))⌝.
Proof using.
  iIntros "H Hγ". iDestruct (hgh_lookup_block with "H Hγ") as %(?&Hfrz&?).
  inversion Hfrz; subst; eauto. iPureIntro; eexists. split; last by eauto.
  congruence.
Qed.

Lemma hgh_modify_block χ σ ζ γ lvs lvs' :
  HGH χ (Some σ) ζ -∗
  lstore_own_elem γ (DfracOwn 1) (Bvblock (Mut, (TagDefault, lvs))) ==∗
  HGH χ (Some σ) (<[γ := Bvblock (Mut, (TagDefault, lvs'))]> ζ) ∗
  lstore_own_elem γ (DfracOwn 1) (Bvblock (Mut, (TagDefault, lvs'))).
Proof using.
  iNamed 1. iNamed "HGHσo". iIntros "Hpto".
  iDestruct (lstore_own_elem_of with "HGHζ Hpto") as %Hγ.
  iDestruct (lstore_own_elem_to_mut with "Hpto") as "Hpto"; auto.
  iMod (lstore_own_update _ _ _ _ with "HGHζ Hpto") as "[HGHζ Hpto]".
  iModIntro. iFrame "Hpto". rewrite /HGH /named.
  repeat iExists _. iFrame. iSplit.
  { iExists _, _. iFrame. iPureIntro; split_and!; eauto.
    { by apply freeze_lstore_insert. }
    { eapply lstore_hybrid_repr_modify_block; eauto. } }
  { iPureIntro; split_and!; eauto.
    { eapply lstore_representable_insert; eauto. }
    { rewrite dom_insert_L subseteq_union_1_L// singleton_subseteq_l.
      eapply lstore_hybrid_repr_lookup_lloc in HGHζrepr; last apply Hγ.
      destruct HGHζfreeze. apply elem_of_dom_2 in HGHζrepr. set_solver. } }
Qed.

Lemma hgh_export_ml_heap χ σ ζ :
  HGH χ (Some σ) ζ -∗
  ∃ ζ' χ' ζfreeze σfull,
    HGH χ' None ζ' ∗
    state_interp σfull ∗
    ⌜σ ⊆ σfull⌝ ∗
    ⌜expose_llocs χ χ'⌝ ∗
    ⌜freeze_lstore ζ ζfreeze⌝ ∗
    ⌜lstore_hybrid_repr χ' ζfreeze σfull ζ'⌝ ∗
    ⌜pub_locs_in_lstore χ' ζ' = ∅⌝.
Proof using.
  iNamed 1. iNamed "HGHσo". iNamed "HGHσ".

  pose proof HGHζrepr as HGHζrepr'.
  pose (ζdel := filter (λ '(k, _), k ∈ dom (lloc_map_pubs χg)) ζg).
  eapply (lstore_hybrid_repr_mut_to_ml_many _ _ _ _ ζdel)
    in HGHζrepr' as (σadd & Hrepr' & Hσadd); eauto.
  2: { eapply map_filter_subseteq. }
  2: { rewrite elem_of_subseteq. intros γ [blk Hγ]%elem_of_dom.
       by eapply map_filter_lookup_Some_1_2 in Hγ. }

  iAssert (state_interp (σ ∪ σadd) ∗ ([∗ map] ℓ↦vs ∈ σadd, ℓ ↦∗ vs))%I
    with "[SIWSfull SIWSsafe]" as "[SIWSfull SIWSsafe]".
  { admit. }

  iExists (ζg ∖ ζdel), χg, ζfreeze, (σ ∪ σadd). iFrame. iSplit.
  { rewrite /HGH /named. iExists _, _. iFrame. iSplit; last (iSplit; iPureIntro).
    { iExists _. iFrame. iPureIntro; split_and!; eauto.

  2: { iPureIntro; split_and!; eauto.
       { eapply map_union_subseteq_l; eauto. }
       {

  (* iExists ζg, χg, ζfreeze, σfull. iNamed "HGHσ". iFrame. iSplit. *)
  (* 2: { iPureIntro; split_and!; eauto. eapply map_union_subseteq_l; eauto. } *)
  (* rewrite /HGH /named. iExists _, _. iFrame. iSplit; last (iSplit; iPureIntro). *)
  (* { iExists _. iFrame. iSplit; iPureIntro; eauto. *)
  (*   eapply map_eq. intros γ. rewrite lookup_empty. *)
  (*   Search pub_locs_in_lstore lookup. eapply pub_locs_in_lstore_ *)


 (* apply elem_of_subseteq. *)
    (* intros ℓ Hℓ. *)
    (* apply codom_spec in Hℓ as (γ&Hγ). *)
    (* apply pub_locs_in_lstore_lookup in Hγ as (Hγ&?). *)
    (* assert (ℓ ∈ lloc_map_pub_locs χg). *)
    (* { apply elem_of_lloc_map_pub_locs; eauto. } *)
    (* assert (σ !! ℓ = None) as ?%not_elem_of_dom. *)
    (* { apply elem_of_dom in Hγ as (?&?). *)
    (*   eapply lstore_hybrid_repr_lookup_pub_lloc_notin; eauto. } *)
    (* map_disjoint_dom. set_solver. } *)
  (* { eapply expose_llocs_refl; eauto. } *)
  (* { destruct Hχexp as [Hdom1 _]. rewrite -Hdom1. transitivity (dom ζ); auto. *)
  (*   destruct HGHζfreeze as [Hdom2 _]. rewrite Hdom2. *)
  (*   destruct HGHζrepr as (?&->&_&_&_). set_solver. } *)
Qed.

Lemma lstore_hybrid_repr_loc_in_pub_locs χ ζfreeze σ ζ ℓ :
  lstore_hybrid_repr χ ζfreeze σ ζ →
  ℓ ∈ dom σ →
  ℓ ∈ lloc_map_pub_locs χ.
Proof using.
  intros (ζσ&->&?&Hblks&Hstore) Hℓ.
  apply Hblks in Hℓ as (γ&?&?). eapply elem_of_lloc_map_pub_locs; eauto.
Qed.

Lemma gen_heap_valid_many σ σ' :
  gen_heap_interp σ -∗
  ([∗ map] ℓ↦vs ∈ σ', ℓ ↦∗ vs) -∗
  ⌜σ' ⊆ σ⌝.
Proof using.
  induction σ' using map_ind; iIntros "H Hm".
  { iPureIntro. eapply map_empty_subseteq. }
  { iDestruct (big_sepM_insert with "Hm") as "[Hℓ Hm]"; auto.
    iDestruct (IHσ' with "H Hm") as %Hsub.
    iDestruct (gen_heap_valid with "H Hℓ") as %Hℓ.
    iPureIntro. eapply insert_subseteq_l; eauto. }
Qed.

Lemma hgh_import_ml_interp χold σ ζold χ ζ ζnewimm :
  lloc_map_mono χold χ →
  lstore_hybrid_repr χ ζ σ (ζold ∪ ζnewimm) →
  is_private_blocks χ ζnewimm →
  dom ζ ⊆ dom χ →
  ζold ##ₘ ζnewimm →
  HGH χold None ζold -∗
  state_interp σ ==∗
  ∃ σ', HGH χ (Some σ') ζ ∗ ⌜σ' ⊆ σ⌝.
Proof using.
  intros Hχ Hstore Hpriv Hsub Hdisj.
  iNamed 1. iNamed "HGHσo". iIntros "Hσ".
  iAssert (⌜σsafe ⊆ σ⌝)%I as %Hσsub;
    first by iApply (gen_heap_valid_many with "Hσ HGHσsafe").
  (* lstore_hybrid_repr: view the σsafe part of σ as being part of ζ.
     (effectively this is an iterated "ml to mut" step for all elements of σsafe. *)
  destruct Hχ as [? Hχinj].
  pose proof (lstore_hybrid_repr_ml_to_mut_many _ _ _ _ _
    Hχinj Hσsub Hstore) as (ζadd & HH & HHdisj).
  (* now update the authoritative ghost state of ζ accordingly *)
  iMod (lstore_own_insert_many _ ζnewimm with "HGHζ") as "(HGHζ & HGHζnewimm)";
    first done.
  iMod (lstore_own_insert_many _ ζadd with "HGHζ") as "(HGHζ & HGHζadd)";
    first (map_disjoint_dom; set_solver).
  (* update the authoritative part of χ *)
  iMod (lloc_own_mono with "HGHχ") as "HGHχ"; first done.
  (* we have state_interp_with_safekeeping where σsafe is the safekeeping. easy. *)
  iAssert (state_interp_with_safekeeping σ (σ ∖ σsafe)) with "[Hσ HGHσsafe]" as "Hσ".
  { rewrite /state_interp_with_safekeeping /named. iExists σsafe.
    iFrame. iPureIntro; split_and.
    { rewrite map_union_comm. 2: by eapply map_disjoint_difference_l.
      rewrite map_difference_union//. }
    { by eapply map_disjoint_difference_l. } }
  (* now extend the safekeeping part with extra points-tos for any new
     extra ("garbage") loc that appeared in χ, in order to match the
     requirements of HGH. Such points-tos have dummy values attach to them. *)
  iMod (siws_alloc_safe_as_needed _ _ (lloc_map_pub_locs χ) with "Hσ")
    as (σfull) "(Hσ & % & %)".
  { apply elem_of_subseteq. intros ℓ Hℓ.
    by eapply lstore_hybrid_repr_loc_in_pub_locs; first eapply Hstore. }
  (* terminate the proof. *)
  iModIntro. iExists (σ ∖ σsafe). iSplit.
  2: { iPureIntro. by eapply map_subseteq_difference_l. }
  rewrite /HGH /named. iExists _, _. iFrame. iSplit.
  { iExists _, σfull. iFrame "Hσ". iPureIntro; split_and!; eauto.
    apply freeze_lstore_refl. }
  iPureIntro; split_and!; eauto. apply expose_llocs_refl; eauto.
Qed.

End HGH.
