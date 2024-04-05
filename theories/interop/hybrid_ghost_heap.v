From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From transfinite.base_logic.lib Require Import ghost_map ghost_var gen_heap.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props.
From melocoton.ml_lang Require Import lang primitive_laws.
From melocoton.interop Require Export basics basics_resources.

Section HGH.
Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!wrapperBasicsG Σ}.

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
  - apply map_disjoint_dom. set_solver.
  - split; set_solver.
  - intros ?. set_solver.
Qed.

Lemma lstore_hybrid_repr_lookup_loc χ ζfreeze σ ζ ℓ vs γ :
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lloc_map_inj χ →
  σ !! ℓ = Some (Some vs) →
  χ !! γ = Some (LlocPublic ℓ) →
  ∃ lvs, ζfreeze !! γ = Some (Bvblock (Mut, (TagDefault, lvs))) ∧
         Forall2 (is_val χ ζfreeze) vs lvs.
Proof using.
  intros (ζσ & Hfreezeeq & ? & Hstore_blocks & Hstore) Hχinj Hσ Hχ.
  edestruct is_store_blocks_has_loc as (ll & Hlχ & Hγζ);
    [apply Hstore_blocks|apply Hσ|..].
  assert (ll = γ) as -> by (eapply Hχinj; eauto). clear Hlχ.
  apply elem_of_dom in Hγζ. destruct Hγζ as [bb Hζσγ].
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
  intros (?&?&?&?&?) ?. eapply block_sim_arr_of_auth; eauto.
Qed.

Lemma block_sim_arr_auth_is_val' χ ζfreeze σ ζ lvs vs :
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lloc_own_auth χ -∗
  lstore_own_auth ζ -∗
  lvs ~~∗ vs -∗
  ⌜Forall2 (is_val χ ζfreeze) vs lvs⌝.
Proof using.
  intros (?&->&?&?&?). iApply block_sim_arr_auth_is_val; eauto.
Qed.

Lemma lstore_hybrid_repr_ml_to_mut χ ζfreeze σ ζ ℓ γ vs lvs :
  lloc_map_inj χ →
  χ !! γ = Some (LlocPublic ℓ) →
  ζfreeze !! γ = Some (Bvblock (Mut, (TagDefault, lvs))) →
  σ !! ℓ = Some (Some vs) →
  ζ !! γ = None →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lstore_hybrid_repr χ ζfreeze (<[ℓ:=None]> σ)
    (<[γ:=Bvblock (Mut, (TagDefault, lvs))]> ζ).
Proof using.
  intros Hχinj ? Hfγ ? ? (ζσ & -> & ? & ? & ?).
  exists (delete γ ζσ). split_and!.
  - symmetry. apply union_delete_insert.
    by apply lookup_union_Some_inv_l in Hfγ.
  - apply map_disjoint_insert_r_2. 1: apply lookup_delete.
    by apply map_disjoint_delete_l.
  - eapply is_store_blocks_discard_loc; eauto.
  - eapply is_store_discard_loc; eauto.
Qed.

Lemma lstore_hybrid_repr_mut_to_ml χ ζfreeze σ ζ ℓ vs γ lvs :
  lloc_map_inj χ →
  χ !! γ = Some (LlocPublic ℓ) →
  σ !! ℓ = Some None →
  ζ !! γ = Some (Bvblock (Mut, (TagDefault, lvs))) →
  Forall2 (is_val χ ζfreeze) vs lvs →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lstore_hybrid_repr χ ζfreeze (<[ℓ:=Some vs]> σ) (delete γ ζ).
Proof using.
  intros ? ? ? ? ? (ζσ&->&?&?&?).
  exists (<[γ:=Bvblock (Mut, (TagDefault, lvs))]> ζσ). split_and!.
  - erewrite (union_insert_delete ζσ ζ). 2: eapply map_disjoint_Some_r. all: eauto.
  - apply map_disjoint_insert_l_2. 1: apply lookup_delete.
    by apply map_disjoint_delete_r.
  - eapply is_store_blocks_restore_loc; eauto.
  - eapply is_store_restore_loc; eauto. 1: eapply lookup_union_Some_r; eauto.
    by constructor.
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

Lemma lstore_hybrid_repr_expose_lloc χ ζfreeze σ ζ γ :
  lloc_map_inj χ →
  χ !! γ = Some LlocPrivate →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  ∃ ℓ, ℓ ∉ lloc_map_pub_locs χ ∧
       ℓ ∉ dom σ ∧
       lstore_hybrid_repr (<[γ:=LlocPublic ℓ]> χ) ζfreeze (<[ℓ:=None]> σ) ζ.
Proof using.
  intros ? ? (ζσ&->&?&Hstore_blocks&?).
  pose (fresh_locs (lloc_map_pub_locs χ)) as ℓ. exists ℓ.
  assert (ℓ ∉ lloc_map_pub_locs χ).
  { intros Hℓ. apply (fresh_locs_fresh (lloc_map_pub_locs χ) 0 ltac:(lia)).
    rewrite /loc_add Z.add_0_r //. }
  assert (ℓ ∉ dom σ).
  { intros Hℓ. destruct Hstore_blocks as [HH1 _].
    destruct (HH1 _ Hℓ) as (γ'&Hγ'). by apply elem_of_lloc_map_pub_locs_1 in Hγ'. }
  split_and!; auto. exists ζσ. split_and!; eauto.
  - eapply is_store_blocks_expose_lloc; eauto.
  - eapply is_store_expose_lloc; eauto.
Qed.

Lemma lstore_hybrid_repr_freeze_block χ ζfreeze σ ζ γ b1 b2 :
  freeze_block b1 b2 →
  χ !! γ = Some LlocPrivate →
  ζ !! γ = Some b1 →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lstore_hybrid_repr χ (<[γ:=b2]> ζfreeze) σ
    (<[γ:=b2]> ζ).
Proof using.
  intros Hfreeze ? ? (ζσ&->&?&?&?). exists ζσ. split_and!; eauto.
  - rewrite insert_union_r. 1: done. eapply map_disjoint_Some_r; eauto.
  - apply map_disjoint_insert_r. split; last done. by eapply map_disjoint_Some_l.
  - eapply is_store_freeze_lloc; eauto.
    eapply lookup_union_Some_r; eauto.
Qed.

Lemma lstore_hybrid_repr_alloc_block χ ζfreeze σ ζ γ blk :
  χ !! γ = None →
  ζfreeze !! γ = None →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lstore_hybrid_repr (<[γ:=LlocPrivate]> χ)
    (<[γ:=blk]> ζfreeze) σ (<[γ:=blk]> ζ).
Proof using.
  intros ? Hζγ (ζσ&->&?&?&?). exists ζσ.
  apply lookup_union_None in Hζγ as [? ?].
  split_and!.
  - rewrite insert_union_r//.
  - apply map_disjoint_insert_r; split; auto.
  - eapply is_store_blocks_alloc_block; eauto.
  - eapply is_store_alloc_block; eauto.
Qed.

Lemma lstore_hybrid_repr_modify_block χ ζfreeze σ ζ γ blk blk' :
  ζ !! γ = Some blk →
  mutability blk = Mut →
  lstore_hybrid_repr χ ζfreeze σ ζ →
  lstore_hybrid_repr χ (<[γ:=blk']> ζfreeze) σ (<[γ:=blk']> ζ).
Proof.
  intros Hγ ? Hh.
  pose proof (lstore_hybrid_repr_lookup_lloc _ _ _ _ _ _ Hh Hγ) as Hγf.
  destruct Hh as (ζσ&->&Hdisj&Hstore_blocks&Hstore). exists ζσ. split_and!; eauto.
  - rewrite insert_union_r; first done. by erewrite map_disjoint_Some_l.
  - eapply map_disjoint_dom. erewrite dom_insert_lookup; last by eexists.
    by eapply map_disjoint_dom.
  - eapply is_store_modify_priv_block; eauto. intros ℓ Vs Hχ Hσ.
    assert (γ ∉ dom ζσ) as Hnin.
    { apply elem_of_dom_2 in Hγ. apply map_disjoint_dom in Hdisj. set_solver. }
    destruct Hstore_blocks as [_ HH2]. apply Hnin, HH2; eauto.
Qed.

Definition HGH (χ : lloc_map) (σo : option store) (ζ : lstore) : iProp Σ :=
  ∃ (ζg : lstore) (χg : lloc_map),
  "HGHζ" ∷ lstore_own_auth ζg ∗
  "HGHχ" ∷ lloc_own_auth χg ∗
  "HGHσo" ∷ match σo with
  | None =>
    "[-> ->]" ∷ ⌜ζg = ζ ∧ χg = χ⌝
  | Some σ => ∃ ζfreeze,
    "HGHσ" ∷ state_interp σ ∗
    "%HGHζfreeze" ∷ ⌜freeze_lstore ζ ζfreeze⌝ ∗
    "%HGHζrepr" ∷ ⌜lstore_hybrid_repr χg ζfreeze σ ζg⌝
  end ∗
  "HGHχNone" ∷ ([∗ map] _↦ℓ ∈ pub_locs_in_lstore χg ζg, ℓ ↦M/) ∗
  "%Hχexp" ∷ ⌜expose_llocs χ χg⌝ ∗
  "%Hother_blocks" ∷ ⌜dom ζ ⊆ dom χ⌝.

Lemma hgh_dom_lstore_sub χ σo ζ : HGH χ σo ζ -∗ ⌜dom ζ ⊆ dom χ⌝.
Proof using. iNamed 1. eauto. Qed.

Lemma hgh_χ_inj χ ζ : HGH χ None ζ -∗ ⌜lloc_map_inj χ⌝.
Proof using. iNamed 1. iNamed "HGHσo". iPureIntro. apply Hχexp. Qed.

Lemma hgh_pointsto_has_lloc χ σ ζ ℓ vs :
  HGH χ (Some σ) ζ -∗
  ℓ ↦∗ vs -∗
  ∃ γ, γ ~ℓ~ ℓ.
Proof using.
  iIntros "H Hpto". iNamed "H". iNamed "HGHσo".
  iDestruct (gen_heap_valid with "HGHσ Hpto") as %Hℓ.
  destruct HGHζrepr as (? & ? & ? & ? & ?).
  edestruct is_store_blocks_has_loc as (γ & Hχγ & Hγ); eauto; [].
  iExists γ. by iApply lloc_own_auth_get_pub.
Qed.

Lemma hgh_block_sim_is_val χ ζ vs lvs :
  HGH χ None ζ -∗
  lvs ~~∗ vs -∗
  ⌜Forall2 (is_val χ ζ) vs lvs⌝.
Proof using.
  iNamed 1. iIntros "Hsim". iNamed "HGHσo".
  iDestruct (block_sim_arr_auth_is_val' with "HGHχ HGHζ Hsim") as %?; eauto.
  apply lstore_hybrid_repr_refl.
Qed.

Lemma hgh_block_sim_of χ ζ σ vs lvs :
  Forall2 (is_val χ ζ) vs lvs →
  HGH χ (Some σ) ζ -∗
  lvs ~~∗ vs.
Proof using.
  intros Hvs. iNamed 1. iNamed "HGHσo".
  iApply (block_sim_arr_of_auth' with "HGHχ HGHζ"); eauto.
  eapply Forall2_impl; first done. intros ? ? ?.
  eapply is_val_freeze; eauto. eapply is_val_expose_llocs; eauto.
Qed.

Local Lemma interp_ML_discarded_locs_pub χpub (σ:store) :
    gen_heap_interp σ
 -∗ ([∗ map] ℓ ∈ χpub, ℓ ↦M/)
 -∗ ⌜map_Forall (λ (_ : nat) (ℓ : loc), σ !! ℓ = Some None) χpub⌝.
Proof using.
  induction χpub as [|k l χpub Hin IH] using map_ind; iIntros "HH HK".
  - iPureIntro. apply map_Forall_empty.
  - iPoseProof (big_sepM_insert) as "[HL _]". 1: apply Hin.
    iPoseProof ("HL" with "HK") as "[H1 H2]".
    iPoseProof (IH with "HH H2") as "%HIH".
    iPoseProof (gen_heap_valid with "HH H1") as "%Hv".
    iPureIntro. apply map_Forall_insert. 1: done. split; done.
Qed.

Lemma hgh_discarded_locs_pub χ σ ζ :
  HGH χ None ζ -∗
  state_interp σ -∗
  ⌜map_Forall (λ (_ : nat) (ℓ : loc), σ !! ℓ = Some None) (pub_locs_in_lstore χ ζ)⌝.
Proof using.
  iNamed 1. iNamed "HGHσo". iIntros "Hσ".
  by iApply (interp_ML_discarded_locs_pub with "Hσ HGHχNone").
Qed.

Lemma hgh_empty :
  lstore_own_auth ∅ -∗
  lloc_own_auth ∅ -∗
  HGH ∅ None ∅.
Proof using.
  iIntros "Hζ Hχ". rewrite /HGH /named. iExists ∅, ∅.
  iFrame. rewrite pub_locs_in_lstore_empty big_sepM_empty.
  iPureIntro; split_and!; eauto.
  - by apply expose_llocs_refl.
  - set_solver.
Qed.

Lemma hgh_ml_to_mut χ σ ζ ℓ γ vs :
  HGH χ (Some σ) ζ -∗
  ℓ ↦∗ vs -∗
  γ ~ℓ~ ℓ ==∗
  ∃ lvs,
    HGH χ (Some (<[ℓ := None]> σ)) ζ ∗
    lstore_own_elem γ (DfracOwn 1) (Bvblock (Mut, (TagDefault, lvs))) ∗
    lvs ~~∗ vs.
Proof using.
  iIntros "H Hℓ #Hsim". iNamed "H". iNamed "HGHσo".
  iDestruct (gen_heap_valid with "HGHσ Hℓ") as %Hσℓ.
  iDestruct (lloc_own_pub_of with "HGHχ Hsim") as %Hχγ.
  iAssert (⌜ζg !! γ = None⌝)%I with "[HGHχNone Hℓ]" as %Hζγ.
  { destruct (ζg !! γ) as [b|] eqn:Hb; [iExFalso|done].
    iDestruct (big_sepM_lookup with "HGHχNone") as "Hℓ'".
    { eapply pub_locs_in_lstore_lookup; eauto. eapply elem_of_dom; eauto. }
    by iDestruct (gen_heap.mapsto_agree with "Hℓ Hℓ'") as %?. }
  edestruct lstore_hybrid_repr_lookup_loc as (lvs & Hζfγ & Hlvs); eauto; [].
  iAssert (lvs ~~∗ vs) as "#Hblock".
  1: by iApply (block_sim_arr_of_auth' with "HGHχ HGHζ").
  iMod (gen_heap_update _ _ _ None with "HGHσ Hℓ") as "[HGHσ Hℓ]".
  iMod (lstore_own_insert _ γ (Bvblock (Mut, _)) with "HGHζ") as "(HGHζ & Hz)";
    first done.
  iModIntro. iExists lvs. iFrame "Hblock Hz".
  rewrite /HGH /named. iExists _, _. iFrame. iSplit. 2: iSplit.
  2: { rewrite (pub_locs_in_lstore_insert_lstore_pub _ _ _ ℓ) //.
       iApply big_sepM_insert; eauto. by iFrame. }
  all: iPureIntro; eauto.
  { eexists. split; eauto. eapply lstore_hybrid_repr_ml_to_mut; eauto. }
Qed.

Lemma hgh_mut_to_ml χ σ ζ ℓ γ lvs vs :
  HGH χ (Some σ) ζ -∗
  lstore_own_elem γ (DfracOwn 1) (Bvblock (Mut, (TagDefault, lvs))) -∗
  γ ~ℓ~ ℓ -∗
  lvs ~~∗ vs
  ==∗
  HGH χ (Some (<[ℓ:=Some vs]> σ)) ζ ∗
  ℓ ↦∗ vs.
Proof using.
  iIntros "H Hγ #Hsim #Hblksim". iNamed "H". iNamed "HGHσo".
  iDestruct (lloc_own_pub_of with "HGHχ Hsim") as %Hγℓ.
  iDestruct (lstore_own_elem_of with "HGHζ Hγ") as %Hζγ.
  iAssert (⌜σ !! ℓ = Some None⌝)%I with "[Hγ HGHχNone HGHσ]" as %Hσℓ.
  { iDestruct (big_sepM_lookup with "HGHχNone") as "Hℓ".
    { eapply pub_locs_in_lstore_lookup; eauto. eapply elem_of_dom; eauto. }
    by iDestruct (gen_heap_valid with "HGHσ Hℓ") as %?. }
  iDestruct (block_sim_arr_auth_is_val' with "HGHχ HGHζ Hblksim") as %Hsim;
    try done; [].
  iDestruct (big_sepM_delete _ _ _ ℓ with "HGHχNone") as "[Hℓ HGHχNone]".
  { eapply pub_locs_in_lstore_lookup; eauto. eapply elem_of_dom; eauto. }
  iMod (gen_heap_update _ _ _ (Some vs) with "HGHσ Hℓ") as "[HGHσ Hℓ]".
  iDestruct (lstore_own_elem_to_mut with "Hγ") as "Hγ"; first done.
  iMod (lstore_own_delete with "HGHζ Hγ") as "HGHζ".
  iModIntro. iFrame "Hℓ". rewrite /HGH /named.
  iExists _, _. iFrame. iSplit. 2: iSplit.
  2: by rewrite pub_locs_in_lstore_delete_lstore //.
  all: iPureIntro; eauto.
  { exists ζfreeze. split; eauto. eapply lstore_hybrid_repr_mut_to_ml; eauto. }
Qed.

Lemma hgh_expose_lloc χ σ ζ γ :
  HGH χ (Some σ) ζ -∗ γ ~ℓ~/ ==∗
  ∃ ℓ, ⌜ℓ ∉ dom σ⌝ ∗ HGH χ (Some (<[ℓ:=None]> σ)) ζ ∗ γ ~ℓ~ ℓ.
Proof using.
  iIntros "H Hpriv". iNamed "H". iNamed "HGHσo".
  iDestruct (lloc_own_priv_of with "HGHχ Hpriv") as %Hχγ.
  edestruct lstore_hybrid_repr_expose_lloc as (ℓ & Hℓ & Hℓσ & Hrepr); eauto; [].
  iMod (lloc_own_expose with "HGHχ Hpriv") as "[HGHχ Hpriv]"; first done.
  iMod (gen_heap_alloc _ ℓ None with "HGHσ") as "(HGHσ & HℓNone & _)".
  1: by eapply not_elem_of_dom_1.
  iPoseProof (big_sepM_insert _ _ γ ℓ with "[$HGHχNone $HℓNone]") as "HGHχNone".
  { eapply map_filter_lookup_None. left. eapply lloc_map_pubs_lookup_None; eauto. }
  iModIntro. iExists ℓ. iSplit; first done. iFrame "Hpriv". rewrite /HGH /named.
  iExists _, _. iFrame. iSplit. 2: iSplit.
  2: iApply (big_sepM_subseteq with "HGHχNone");
    eapply pub_locs_in_lstore_insert_pub_sub.
  all: iPureIntro; split_and?; eauto.
  { eapply expose_llocs_trans; first done. eapply expose_llocs_insert; eauto. }
Qed.

Lemma hgh_freeze_block χ σ ζ γ b1 b2:
  freeze_block b1 b2 →
  HGH χ (Some σ) ζ -∗
  lstore_own_elem γ (DfracOwn 1) b1 -∗
  γ ~ℓ~/
  ==∗
  HGH χ (Some σ) ζ ∗
  lstore_own_elem γ (DfracOwn 1) b2 ∗
  γ ~ℓ~/.
Proof using.
  (* TODO: Fix this proof as it does not work with freeze_block_refl *)
  iIntros (Hfreeze) "H Hγ Hfresh".
  iNamed "H". iNamed "HGHσo".
  iDestruct (lstore_own_elem_of with "HGHζ Hγ") as %?.
  iDestruct (lloc_own_priv_of with "HGHχ Hfresh") as %?.
  assert (mutability b1 = Mut). { destruct Hfreeze; easy. }
  iDestruct (lstore_own_elem_to_mut with "Hγ") as "Hγ"; first done.
  iMod (lstore_own_update _ _ _ b2 with "HGHζ Hγ") as "(HGHζ & Hγ)".
  iModIntro. iFrame "Hγ Hfresh". rewrite /HGH /named. iExists _, _. iFrame.
  iSplit. 2: iSplit.
  2: { rewrite pub_locs_in_lstore_insert_existing; eauto. by eapply elem_of_dom_2. }
  all: iPureIntro; eauto.
  { exists (<[γ:=b2]> ζfreeze). split.
    { eapply freeze_lstore_freeze_lloc; eauto.
      by eapply lstore_hybrid_repr_lookup_lloc. }
    { eapply lstore_hybrid_repr_freeze_block; eauto. } }
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
  iExists _, _. iFrame. iSplit. 2: iSplit.
  2: rewrite pub_locs_in_lstore_alloc_priv; eauto.
  all: iPureIntro.
  { exists (<[γ := blk]> ζfreeze). split.
    { by eapply freeze_lstore_insert. }
    { eapply lstore_hybrid_repr_alloc_block; eauto.
      destruct HGHζfreeze as [? _]. not_elem_of_dom. } }
  { split; last set_solver. eapply expose_llocs_insert_both; eauto. }
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
  inversion Hfrz; subst; eauto.
Qed.

Lemma hgh_modify_block χ σ ζ γ blk blk' :
  mutability blk = Mut →
  HGH χ (Some σ) ζ -∗
  lstore_own_elem γ (DfracOwn 1) blk ==∗
  HGH χ (Some σ) (<[γ := blk']> ζ) ∗
  lstore_own_elem γ (DfracOwn 1) blk'.
Proof using.
  intros Hmut. iNamed 1. iNamed "HGHσo". iIntros "Hpto".
  iDestruct (lstore_own_elem_of with "HGHζ Hpto") as %Hγ.
  iDestruct (lstore_own_elem_to_mut with "Hpto") as "Hpto"; auto.
  iMod (lstore_own_update _ _ _ blk' with "HGHζ Hpto") as "[HGHζ Hpto]".
  iModIntro. iFrame "Hpto". rewrite /HGH /named.
  repeat iExists _. iFrame. iSplit. 2: iSplit.
  2: { rewrite pub_locs_in_lstore_insert_existing //. by eapply elem_of_dom_2. }
  all: iPureIntro.
  { eexists. split; first by apply freeze_lstore_insert.
    eapply lstore_hybrid_repr_modify_block; eauto. }
  { split; eauto. rewrite dom_insert_L subseteq_union_1_L// singleton_subseteq_l.
    eapply lstore_hybrid_repr_lookup_lloc in HGHζrepr; last apply Hγ.
    destruct HGHζfreeze. apply elem_of_dom_2 in HGHζrepr. set_solver. }
Qed.

Lemma hgh_export_ml_heap χ σ ζ :
  HGH χ (Some σ) ζ -∗
  ∃ ζ' χ' ζfreeze,
    HGH χ' None ζ' ∗
    state_interp σ ∗
    ⌜expose_llocs χ χ'⌝ ∗
    ⌜freeze_lstore ζ ζfreeze⌝ ∗
    ⌜lstore_hybrid_repr χ' ζfreeze σ ζ'⌝.
Proof using.
  iNamed 1. iNamed "HGHσo".
  iExists ζg, χg, ζfreeze. iFrame. iSplit; last by eauto.
  rewrite /HGH /named. iExists _, _. iFrame. iPureIntro; split_and!; eauto.
  { eapply expose_llocs_refl; eauto. }
  { destruct Hχexp as [Hdom1 _]. rewrite -Hdom1. transitivity (dom ζ); auto.
    destruct HGHζfreeze as [Hdom2 _]. rewrite Hdom2.
    destruct HGHζrepr as (?&->&_&_&_). set_solver. }
Qed.

Lemma hgh_import_ml_interp χold σ ζold χ ζ ζnewimm :
  lloc_map_mono χold χ →
  lstore_hybrid_repr χ ζ σ (ζold ∪ ζnewimm) →
  is_private_blocks χ ζnewimm →
  dom ζ ⊆ dom χ →
  ζold ##ₘ ζnewimm →
  HGH χold None ζold -∗
  state_interp σ ==∗
  HGH χ (Some σ) ζ.
Proof using.
  intros Hχ Hstore Hpriv Hsub Hdisj.
  iNamed 1. iNamed "HGHσo". iIntros "Hσ".
  iMod (lstore_own_insert_many _ ζnewimm with "HGHζ") as "(HGHζ & HGHζnewimm)";
    first done.
  iMod (lloc_own_mono with "HGHχ") as "HGHχ"; first done.
  iModIntro. rewrite /HGH /named. iExists _, _. iFrame. iSplit. 2: iSplit.
  2: { rewrite pub_locs_in_lstore_insert_priv_store //.
       erewrite pub_locs_in_lstore_mono at 1; [| eauto..]; []. iFrame. }
  all: iPureIntro; split_and?; eauto.
  { eexists. split; eauto. apply freeze_lstore_refl. }
  { apply expose_llocs_refl; eauto. }
Qed.

End HGH.
