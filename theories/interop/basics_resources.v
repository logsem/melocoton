From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props.
From melocoton.interop.extra_ghost_state Require Import persistent_ghost_map.
From melocoton.ml_lang Require Import lang.
From melocoton.interop Require Export basics.

Local Program Instance LstorePGMData : PGMData := {
  K := lloc;
  V := block;
  Fpers := block_get_header;
  Pmap m := True;
}.
Next Obligation. eauto. Qed.
Next Obligation. done. Qed.

Local Program Instance LlocPGMData : PGMData := {
  K := lloc;
  V := lloc_visibility;
  Fpers := lloc_visibility_fid;
  Pmap := lloc_map_inj;
}.
Next Obligation.
  intros m1 m2 H1 H2.
  by eapply lloc_map_mono_inj_backwards.
Qed.
Next Obligation. intros ???? []%lookup_empty_Some. Qed.

Class wrapperBasicsGpre `{SI: indexT} Σ := WrapperBasicsGpre {
  wrapperG_lstoreG :> pgmG Σ LstorePGMData;
  wrapperG_lloc_mapG :> pgmG Σ LlocPGMData;
  wrapperG_addr_lvalG :> ghost_mapG Σ addr lval;
}.

Class wrapperBasicsG `{SI: indexT} Σ := WrapperBasicsG {
  wrapperG_inG :> wrapperBasicsGpre Σ;
  wrapperG_γζvirt : gname;
  wrapperG_γχvirt : gname;
  wrapperG_γroots_map : gname;
}.

Definition wrapperBasicsΣ {SI: indexT} : gFunctors :=
  #[pgmΣ LstorePGMData; pgmΣ LlocPGMData; ghost_mapΣ addr lval].

Global Instance subG_wrapperBasicsGpre `{SI: indexT} Σ :
  subG wrapperBasicsΣ Σ → wrapperBasicsGpre Σ.
Proof. solve_inG. Qed.


Section BasicsResources.
Context `{SI: indexT}.
Context `{!wrapperBasicsG Σ}.

(* Ghost state for [lloc_map] *)

Definition lloc_own_priv dq (γ : lloc) fid : iProp Σ :=
  γ □↪[wrapperG_γχvirt]{dq} (LlocPrivate fid).

Definition lloc_own_foreign (γ : lloc) (id : nat) : iProp Σ :=
  γ □↪[wrapperG_γχvirt]□ (LlocForeign id).

Definition lloc_own_pub (γ : lloc) fid (ℓ : loc) : iProp Σ :=
  γ □↪[wrapperG_γχvirt]□ LlocPublic fid ℓ.

Definition lloc_own_fid (γ : lloc) fid : iProp Σ :=
  γ □↪[wrapperG_γχvirt]= fid.

Instance lloc_own_pub_persistent γ fid ℓ : Persistent (lloc_own_pub γ fid ℓ).
Proof using. apply _. Qed.

Instance lloc_own_foreign_persistent γ id : Persistent (lloc_own_foreign γ id).
Proof using. apply _. Qed.

Instance lloc_own_fid_persistent γ id : Persistent (lloc_own_fid γ id).
Proof using. apply _. Qed.

Definition lloc_own_auth (χ : lloc_map) : iProp Σ :=
  "Hχgmap" ∷ pgm_auth wrapperG_γχvirt 1 χ ∗
  "Hχpubs" ∷ ([∗ map] γ↦ℓ ∈ (lloc_map_pubs χ), ∃ fid, lloc_own_pub γ fid ℓ) ∗
  "Hχforeign" ∷ ([∗ map] γ↦id ∈ (lloc_map_foreign χ), lloc_own_foreign γ id) ∗
  "#Hχpers" ∷ ([∗ map] γ↦id ∈ χ, lloc_own_fid γ (lloc_visibility_fid id)).

Notation "γ ~ℓ~ ℓ @ fid" := (lloc_own_pub γ fid ℓ)
  (at level 20, format "γ  ~ℓ~  ℓ  @  fid").
Notation "γ ~ℓ~/ @ fid" := (lloc_own_priv (DfracOwn 1) γ fid)
  (at level 20, format "γ  ~ℓ~/  @  fid").
Notation "γ ~ℓ~/{ dq } @ fid" := (lloc_own_priv dq γ fid)
  (at level 20, format "γ  ~ℓ~/{ dq }  @  fid").
Notation "γ ~foreign~ id" := (lloc_own_foreign γ id)
  (at level 20, format "γ  ~foreign~  id").
Notation "γ ~@~ id" := (lloc_own_fid γ id)
  (at level 20, format "γ  ~@~  id").

Lemma lloc_own_auth_get_pub_all χ :
  lloc_own_auth χ -∗
  [∗ map] γ↦ℓ ∈ (lloc_map_pubs χ), ∃ fid, γ ~ℓ~ ℓ @ fid.
Proof using.
  iNamed 1. iApply "Hχpubs".
Qed.

Lemma lloc_own_auth_get_pub χ γ fid ℓ :
  χ !! γ = Some (LlocPublic fid ℓ) →
  lloc_own_auth χ -∗
  γ ~ℓ~ ℓ @ fid.
Proof using.
  intros Hγ. iNamed 1.
  iDestruct (big_sepM_lookup with "Hχpubs") as "(%fid'&HH)"; first eauto.
  iDestruct (pgm_lookup with "Hχgmap HH") as %HH1.
  rewrite HH1 in Hγ; simplify_eq. done.
Qed.

Lemma lloc_own_auth_get_foreign χ γ id :
  χ !! γ = Some (LlocForeign id) →
  lloc_own_auth χ -∗
  γ ~foreign~ id.
Proof using.
  intros Hγ. iNamed 1.
  iApply (big_sepM_lookup with "Hχforeign"); eauto.
Qed.


Lemma lloc_own_auth_get_fid χ γ vis :
  χ !! γ = Some vis →
  lloc_own_auth χ -∗
  γ ~@~ (lloc_visibility_fid vis).
Proof using.
  intros Hγ. iNamed 1.
  iDestruct (big_sepM_lookup with "Hχpers") as "$"; first eauto.
Qed.

Lemma lloc_own_pub_of χ γ fid ℓ :
  lloc_own_auth χ -∗
  γ ~ℓ~ ℓ @ fid -∗
  ⌜χ !! γ = Some (LlocPublic fid ℓ)⌝.
Proof using.
  iIntros "Hχ Hpub". iNamed "Hχ".
  by iDestruct (pgm_lookup with "Hχgmap Hpub") as %?.
Qed.

Lemma lloc_own_priv_of dq χ γ fid :
  lloc_own_auth χ -∗
  γ ~ℓ~/{ dq } @ fid -∗
  ⌜χ !! γ = Some (LlocPrivate fid)⌝.
Proof using.
  iIntros "Hχ Hpub". iNamed "Hχ".
  by iDestruct (pgm_lookup with "Hχgmap Hpub") as %?.
Qed.

Lemma lloc_own_foreign_of χ γ id :
  lloc_own_auth χ -∗
  γ ~foreign~ id -∗
  ⌜χ !! γ = Some (LlocForeign id)⌝.
Proof using.
  iIntros "Hχ Hfor". iNamed "Hχ".
  by iDestruct (pgm_lookup with "Hχgmap Hfor") as %?.
Qed.

Lemma lloc_own_pers_of χ γ id :
  lloc_own_auth χ -∗
  γ ~@~ id -∗
  ⌜∃ vis, id = lloc_visibility_fid vis ∧ χ !! γ = Some vis⌝.
Proof using.
  iIntros "Hχ Hfor". iNamed "Hχ".
  by iDestruct (pgm_lookup_pers with "Hχgmap Hfor") as %?.
Qed.

Lemma lloc_own_expose χ γ ℓ fid :
  ℓ ∉ lloc_map_pub_locs χ →
  lloc_own_auth χ -∗
  γ ~ℓ~/ @ fid ==∗
  lloc_own_auth (<[γ:=LlocPublic fid ℓ]> χ) ∗ γ ~ℓ~ ℓ @ fid.
Proof using.
  iIntros (Hpubs) "Hχ Hγ".
  unfold lloc_own_priv, lloc_own_auth.
  iDestruct (lloc_own_priv_of with "Hχ Hγ") as %Hχγ.
  iNamed "Hχ".
  iMod (pgm_update (D:=LlocPGMData) (LlocPublic fid ℓ) with "Hχgmap Hγ") as "[$ Hγ]".
  1: done.
  1: intros Hinj; by apply expose_llocs_insert.
  iMod (pgm_elem_persist with "Hγ") as "#Hγ".
  iPoseProof (pgm_elem_to_pers with "Hγ") as "#Hγpers".
  iFrame "Hγ". iModIntro. rewrite /named.
  iSplitL "Hχpubs"; last iSplitL.
  { rewrite lloc_map_pubs_insert_pub.
    iApply big_sepM_insert; eauto.
    apply lloc_map_pubs_lookup_None; eauto. }
  { rewrite lloc_map_foreign_insert_pub delete_notin //.
    destruct (lloc_map_foreign χ !! γ) eqn:Heq; try done.
    apply lloc_map_foreign_lookup_Some in Heq; congruence. }
  { destruct  (χ !! γ) eqn:Heq.
    2: by iApply big_sepM_insert.
    rewrite -insert_delete_insert. cbn.
    iApply big_sepM_insert. 1: by eapply lookup_delete.
    cbn.
    iApply (big_sepM_delete (λ k v, k ~@~ lloc_visibility_fid v) χ γ (LlocPrivate fid)); first by simplify_eq.
    done. }
Qed.

Lemma lloc_own_allocate χ γ fid:
  (∀ (γ' : nat) (vis' : lloc_visibility), γ ≠ γ' → χ !! γ' = Some vis' → fid ≠ lloc_visibility_fid vis') →
  ⌜χ !! γ = None⌝ -∗
  lloc_own_auth χ ==∗
  lloc_own_auth (<[γ:=LlocPrivate fid]> χ) ∗ γ ~ℓ~/ @ fid.
Proof using.
  iIntros (Hfresh Hne) "Hχ".
  iNamed "Hχ".
  iMod (pgm_insert with "Hχgmap") as "[Hχmap Hγ]"; first done.
  1: intros H; by apply lloc_map_inj_insert_priv.
  iPoseProof (pgm_elem_to_pers with "Hγ") as "#Hγpers".
  iModIntro. iSplitR "Hγ"; last done.
  iSplitL "Hχmap"; first done. unfold named.
  iSplitL "Hχpubs"; last iSplitL.
  { rewrite lloc_map_pubs_insert_priv delete_notin. 1: done.
    destruct (lloc_map_pubs χ !! γ) eqn:Heq; try done.
    apply lloc_map_pubs_lookup_Some in Heq as (?&Heq); try congruence. }
  { rewrite lloc_map_foreign_insert_priv delete_notin //.
    destruct (lloc_map_foreign χ !! γ) eqn:Heq; try done.
    apply lloc_map_foreign_lookup_Some in Heq; congruence. }
  { iApply big_sepM_insert; first done. by iSplit. }
Qed.

Lemma lloc_own_allocate_foreign χ γ id:
  (∀ (γ' : nat) (vis' : lloc_visibility), γ ≠ γ' → χ !! γ' = Some vis' → id ≠ lloc_visibility_fid vis') →
  ⌜χ !! γ = None⌝ -∗
  lloc_own_auth χ ==∗
  lloc_own_auth (<[γ:=LlocForeign id]> χ) ∗ γ ~foreign~ id.
Proof using.
  iIntros (Hfresh Hne) "Hχ".
  iNamed "Hχ".
  iMod (pgm_insert (D:=LlocPGMData) _ (LlocForeign id) with "Hχgmap") as "[Hχmap Hγ]"; first done.
  1: intros H; by apply lloc_map_inj_insert_foreign.
  iMod (pgm_elem_persist with "Hγ") as "#Hγ".
  iPoseProof (pgm_elem_to_pers with "Hγ") as "#Hγpers".
  iModIntro. iSplitR "Hγ"; last by iApply "Hγ".
  iSplitL "Hχmap"; first done. unfold named.
  iSplitL "Hχpubs"; last iSplitL.
  { rewrite lloc_map_pubs_insert_foreign delete_notin.
    2: destruct (lloc_map_pubs χ !! γ) eqn:Heq; try done; apply lloc_map_pubs_lookup_Some in Heq as (?&Heq); congruence.
    done. }
  { rewrite lloc_map_foreign_insert_foreign.
    iApply big_sepM_insert; eauto.
    destruct (lloc_map_foreign χ !! γ) eqn:Heq; try done.
    apply lloc_map_foreign_lookup_Some in Heq; congruence. }
  { iApply big_sepM_insert; first done. by iSplit. }
Qed.

Lemma lloc_own_mono χ1 χ2 :
  lloc_map_mono χ1 χ2  →
  lloc_own_auth χ1 ==∗
  lloc_own_auth χ2.
Proof using.
  intros (Hmono & Hinj).
  pose (χ2 ∖ χ1) as χdiff.
  assert (χ1 ##ₘ χdiff) as Hdis by by apply map_disjoint_difference_r.
  assert (χ2 = (χ1 ∪ χdiff)) as Heq by by rewrite map_difference_union.
  rewrite Heq in Hinj. rewrite Heq. clear Heq Hmono.
  revert Hinj Hdis.
  induction χdiff as [|k v χdiff Hne IH] using map_ind; intros Hinj Hdisj.
  1: rewrite map_union_empty; iIntros "$ !>"; done.
  iIntros "Hown".
  assert (χ1 !! k = None ∧ χ1 ##ₘ χdiff) as [Hnone Hdisj2] by by apply map_disjoint_insert_r in Hdisj.
  rewrite <- insert_union_r in Hinj; last done.
  iMod (IH with "[Hown]") as "Hown".
  - eapply lloc_map_mono_inj_backwards. split; last done.
    apply insert_subseteq. by eapply lookup_union_None.
  - done.
  - done.
  - rewrite <- insert_union_r; last done.
    destruct v as [fid ℓ|fid|fid].
    + iMod (lloc_own_allocate with "[] Hown") as "(Hown&Hpriv)".
      2: iPureIntro; by eapply lookup_union_None.
      2: iMod (lloc_own_expose with "Hown Hpriv") as "(H&_)".
      3: by rewrite insert_insert.
      * intros γ' vis' Hne' Heq1 Heq2.
        by epose proof (Hinj k γ' _ vis' (ltac:(by rewrite lookup_insert)) (ltac:(by rewrite lookup_insert_ne)) (ltac:(by left))).
      * intros (fid'&γ'&[(?&?)|(Hne2&HH)]%lookup_insert_Some)%elem_of_lloc_map_pub_locs; first done.
        eapply Hne2, Hinj.
        1: by rewrite lookup_insert. 1: by rewrite lookup_insert_ne. right; by eexists.
    + iMod (lloc_own_allocate_foreign with "[] Hown") as "($&Hforeign)".
      3: by iModIntro. 2: iPureIntro; by eapply lookup_union_None.
      intros γ' vis' Hne' Heq1 Heq2.
      by epose proof (Hinj k γ' _ vis' (ltac:(by rewrite lookup_insert)) (ltac:(by rewrite lookup_insert_ne)) (ltac:(by left))).
    + iMod (lloc_own_allocate with "[] Hown") as "($&Hpriv)".
      3: by iModIntro. 2: iPureIntro; by eapply lookup_union_None.
      intros γ' vis' Hne' Heq1 Heq2.
      by epose proof (Hinj k γ' _ vis' (ltac:(by rewrite lookup_insert)) (ltac:(by rewrite lookup_insert_ne)) (ltac:(by left))).
Qed.

Lemma lloc_own_pub_inj γ1 γ2 ℓ1 ℓ2 fid1 fid2 :
    γ1 ~ℓ~ ℓ1 @ fid1
 -∗ γ2 ~ℓ~ ℓ2 @ fid2
 -∗ ⌜γ1 = γ2 ↔ (ℓ1 = ℓ2 ∨ fid1 = fid2)⌝.
Proof.
  iIntros "#Hsim1 #Hsim2".
  destruct (decide (γ1 = γ2)) as [->|Hne].
  { iDestruct (pgm_elem_agree with "Hsim1 Hsim2") as %Heq; simplify_eq;
    iPureIntro; naive_solver. }
  iPoseProof (pgm_lookup_prop (D:=LlocPGMData) (<[γ1 := LlocPublic fid1 ℓ1]> {[γ2 := LlocPublic fid2 ℓ2 ]}) with "[Hsim1 Hsim2]") as "%HH".
  - iApply big_sepM_insert. 1: by rewrite lookup_singleton_ne.
    iSplitL; first by iExists _.
    iApply big_sepM_singleton. by iExists _.
  - iPureIntro; split; first by by intros.
    intros H; eapply HH.
    1: by rewrite lookup_insert.
    1: by rewrite lookup_insert_ne // lookup_singleton.
    destruct H as [-> | ->].
    + right; by eexists.
    + by left.
Qed.

Lemma lloc_own_foreign_inj γ1 γ2 fid1 fid2 :
    γ1 ~foreign~ fid1
 -∗ γ2 ~foreign~ fid2
 -∗ ⌜γ1 = γ2 ↔ fid1 = fid2⌝.
Proof.
  iIntros "#Hsim1 #Hsim2".
  destruct (decide (γ1 = γ2)) as [->|Hne].
  { iDestruct (pgm_elem_agree with "Hsim1 Hsim2") as %Heq; simplify_eq;
    iPureIntro; naive_solver. }
  iPoseProof (pgm_lookup_prop (D:=LlocPGMData) (<[γ1 := LlocForeign fid1]> {[γ2 := LlocForeign fid2]}) with "[Hsim1 Hsim2]") as "%HH".
  - iApply big_sepM_insert. 1: by rewrite lookup_singleton_ne.
    iSplitL; first by iExists _.
    iApply big_sepM_singleton. by iExists _.
  - iPureIntro; split; first by by intros.
    intros H; eapply HH.
    1: by rewrite lookup_insert.
    1: by rewrite lookup_insert_ne // lookup_singleton.
    left; done.
Qed.

Lemma lloc_own_fid_inj γ1 γ2 fid1 fid2 :
    γ1 ~@~ fid1
 -∗ γ2 ~@~ fid2
 -∗ ⌜γ1 = γ2 ↔ fid1 = fid2⌝.
Proof.
  iIntros "#Hsim1 #Hsim2".
  destruct (decide (γ1 = γ2)) as [->|Hne].
  { iDestruct (pgm_pers_agree with "Hsim1 Hsim2") as %Heq; simplify_eq;
    iPureIntro; naive_solver. }
  iDestruct (pgm_lookup_pers_prop (D:=LlocPGMData) (<[γ1 := inr fid1]> {[γ2 := inr fid2]}) with "[Hsim1 Hsim2]") as %(m1&Hdom&Hpmap&Hagree).
  - iApply big_sepM_insert. 1: by rewrite lookup_singleton_ne.
    iSplitL; first by iApply "Hsim1".
    iApply big_sepM_singleton. done.
  - iPureIntro; split; first by by intros.
    intros H.
    rewrite dom_insert_L dom_singleton_L in Hdom.
    destruct (m1 !! γ1) eqn:Heq1.
    2: eapply not_elem_of_dom in Heq1; rewrite Hdom in Heq1; set_solver.
    destruct (m1 !! γ2) eqn:Heq2.
    2: eapply not_elem_of_dom in Heq2; rewrite Hdom in Heq2; set_solver.
    epose proof (Hagree _ _ _ Heq1) as Hagr1.
    rewrite lookup_insert in Hagr1. specialize (Hagr1 eq_refl).
    epose proof (Hagree _ _ _ Heq2) as Hagr2.
    rewrite lookup_insert_ne // lookup_singleton in Hagr2. specialize (Hagr2 eq_refl).
    cbn in *.
    eapply Hpmap. 1-2: done.
    left; by simplify_eq.
Qed.

(* Ghost state for [lstore] *)

Definition lstore_own_elem (γ : lloc) (dq : dfrac) (b : block) :=
  match mutability b with
  | Mut => pgm_elem (D:=LstorePGMData) wrapperG_γζvirt γ dq b
  | Immut => pgm_elem (D:=LstorePGMData) wrapperG_γζvirt γ DfracDiscarded b
  end%I.

Definition lstore_own_head (γ : lloc) (h : block_header) := pgm_pers (D:=LstorePGMData) wrapperG_γζvirt γ h.

Definition lstore_own_mut (γ : lloc) (dq : dfrac) (b : block) :=
  (lstore_own_elem γ dq b ∗ ⌜mutability b = Mut⌝)%I.

Definition lstore_own_immut (γ : lloc) (b : block) :=
  (lstore_own_elem γ (DfracOwn 1) b ∗ ⌜mutability b = Immut⌝)%I.

Definition lstore_own_auth (ζ : lstore) : iProp Σ :=
  "Hζgmap" ∷ pgm_auth (D:=LstorePGMData) wrapperG_γζvirt 1 ζ ∗
  "#Hζimmut" ∷ ([∗ map] γ↦b ∈ (lstore_immut_blocks ζ), lstore_own_immut γ b).

Global Instance lstore_own_immut_persistent γ b :
  Persistent (lstore_own_immut γ b).
Proof using.
  unfold Persistent.
  iIntros "[? %H]". unfold lstore_own_immut, lstore_own_elem.
  rewrite H. rewrite bi.persistently_sep bi.persistently_pure.
  iSplit; auto. by iApply persistent.
Qed.

Global Instance lstore_own_head_persistent γ h :
  Persistent (lstore_own_head γ h).
Proof using. apply _. Qed.

Lemma lstore_own_elem_to_mut γ dq b :
  mutability b = Mut →
  lstore_own_elem γ dq b -∗
  lstore_own_mut γ dq b.
Proof using. intros H. rewrite /lstore_own_mut /lstore_own_elem H. eauto. Qed.

Lemma lstore_own_mut_to_elem γ dq b :
  lstore_own_mut γ dq b -∗
  lstore_own_elem γ dq b.
Proof using. by iIntros "[? _]". Qed.

Lemma lstore_own_elem_to_immut γ dq b :
  mutability b = Immut →
  lstore_own_elem γ dq b -∗
  lstore_own_immut γ b.
Proof using. intros H. rewrite /lstore_own_immut /lstore_own_elem H. eauto. Qed.

Lemma lstore_own_immut_to_elem γ b :
  lstore_own_immut γ b -∗
  lstore_own_elem γ (DfracOwn 1) b.
Proof using. by iIntros "[? _]". Qed.

Lemma lstore_own_auth_get_immut_all ζ :
  lstore_own_auth ζ -∗
  [∗ map] γ↦b ∈ (lstore_immut_blocks ζ), lstore_own_immut γ b.
Proof using.
  iNamed 1. iApply "Hζimmut".
Qed.

Lemma lstore_own_auth_get_immut ζ γ b :
  ζ !! γ = Some b →
  mutability b = Immut →
  lstore_own_auth ζ -∗
  lstore_own_immut γ b.
Proof using.
  intros ? ?. iNamed 1.
  iDestruct (big_sepM_lookup with "Hζimmut") as "?"; eauto.
  by eapply lstore_immut_blocks_lookup_immut.
Qed.

Lemma lstore_own_elem_of ζ γ dq b :
  lstore_own_auth ζ -∗
  lstore_own_elem γ dq b -∗
  ⌜ζ !! γ = Some b⌝.
Proof using.
  iNamed 1. iIntros "He".
  destruct (mutability b) eqn:Hmut; rewrite /lstore_own_elem Hmut;
    by iDestruct (pgm_lookup with "Hζgmap He") as "?".
Qed.

Lemma lstore_own_mut_of ζ γ dq b :
  lstore_own_auth ζ -∗
  lstore_own_mut γ dq b -∗
  ⌜ζ !! γ = Some b ∧ mutability b = Mut⌝.
Proof using.
  iIntros "Ha [H %]".
  by iDestruct (lstore_own_elem_of with "Ha H") as %?.
Qed.

Lemma lstore_own_immut_of ζ γ b :
  lstore_own_auth ζ -∗
  lstore_own_immut γ b -∗
  ⌜ζ !! γ = Some b ∧ mutability b = Immut⌝.
Proof using.
  iIntros "Ha [H %]".
  by iDestruct (lstore_own_elem_of with "Ha H") as %?.
Qed.

Lemma lstore_own_head_of ζ γ h :
  lstore_own_auth ζ -∗
  lstore_own_head γ h -∗
  ⌜∃ b, ζ !! γ = Some b ∧ block_get_header b = h⌝.
Proof using.
  iIntros "Ha Hh". iNamed "Ha".
  iDestruct (pgm_lookup_pers with "Hζgmap Hh") as %(b&Heq&Heq2).
  iPureIntro; cbn in *; eexists; by rewrite Heq Heq2.
Qed.

Lemma lstore_own_insert ζ γ b :
  ζ !! γ = None →
  lstore_own_auth ζ ==∗
  lstore_own_auth (<[γ:=b]> ζ) ∗ lstore_own_elem γ (DfracOwn 1) b.
Proof using.
  iIntros (Hγ). iNamed 1.
  iMod (pgm_insert (D:=LstorePGMData) _ b with "Hζgmap") as "[Hζgmap Helt]"; eauto.
  iFrame "Hζgmap".
  destruct (mutability b) eqn:Hmut.
  { rewrite /lstore_own_elem Hmut. iFrame "Helt".
    rewrite lstore_immut_blocks_insert_mut // delete_notin //; eauto. }
  { iMod (pgm_elem_persist with "Helt") as "#Helt".
    rewrite /lstore_own_elem Hmut. iFrame "Helt".
    iModIntro. rewrite lstore_immut_blocks_insert_immut // big_sepM_insert; eauto.
    iFrame. rewrite /lstore_own_immut /lstore_own_elem Hmut //. eauto. }
Qed.

Lemma lstore_own_insert_many ζ ζnew :
  ζ ##ₘ ζnew →
  lstore_own_auth ζ ==∗
  lstore_own_auth (ζ ∪ ζnew) ∗ [∗ map] γ ↦ b ∈ ζnew, lstore_own_elem γ (DfracOwn 1) b.
Proof using.
  induction ζnew as [|γ b ζnew Hne IH] using map_ind.
  1: intros _; rewrite map_union_empty; iIntros "H !>"; iPoseProof (bi.emp_sep_1 with "H") as "(Hemp&H)"; iFrame "H"; iApply big_sepM_empty; done.
  iIntros (Hdisj) "Hown".
  iMod (IH with "Hown") as "(Hζgmap & Hbs)".
  1: apply map_disjoint_dom; eapply map_disjoint_dom in Hdisj; set_solver.
  assert (ζ !! γ = None) as Hζγ.
  1: eapply map_disjoint_Some_r; first done; apply lookup_insert.
  iMod (lstore_own_insert with "Hζgmap") as "(Hζgmap & Hfrag)".
  1: apply lookup_union_None; split; done.
  rewrite insert_union_r; last done.
  iModIntro.
  iFrame "Hζgmap".
  iApply big_sepM_insert; first done. iFrame.
Qed.

Lemma lstore_own_update ζ γ b b' :
  block_get_header b = block_get_header b' →
  lstore_own_auth ζ -∗
  lstore_own_mut γ (DfracOwn 1) b ==∗
  lstore_own_auth (<[γ:=b']> ζ) ∗ lstore_own_elem γ (DfracOwn 1) b'.
Proof using.
  iIntros (Hhead) "Ha He". iDestruct (lstore_own_mut_of with "Ha He") as %[? _].
  iNamed "Ha". iDestruct "He" as "[He %Hmut]".
  rewrite /lstore_own_elem Hmut.
  iMod (pgm_update with "Hζgmap He") as "[Hζgmap He]".
  1: apply Hhead. 1: done.
  destruct (mutability b') eqn:Hmut'.
  { iFrame. iApply (big_sepM_subseteq with "Hζimmut").
    rewrite lstore_immut_blocks_insert_mut //. apply delete_subseteq. }
  { iMod (pgm_elem_persist with "He") as "#$". iFrame.
    rewrite lstore_immut_blocks_insert_immut //.
    iApply big_sepM_insert; eauto. iModIntro.
    rewrite /lstore_own_immut /lstore_own_elem Hmut'; eauto. }
Qed.

(* Vblock points-to *)

Inductive vblock_access := F | M | I.

Inductive vblock_access_le : vblock_access → vblock_access → Prop :=
  | vblock_access_le_refl a : vblock_access_le a a
  | vblock_access_le_M_F : vblock_access_le M F
  | vblock_access_le_I_F : vblock_access_le I F
  | vblock_access_le_I_M : vblock_access_le I M.

Definition ismut_of_access (acc : vblock_access) : ismut :=
  match acc with
  | F | M => Mut
  | I => Immut
  end.

Definition lstore_own_vblock γ acc dq b : iProp Σ :=
  lstore_own_elem γ dq (Bvblock (ismut_of_access acc, b)) ∗
  match acc with
  | F => ∃ fid, γ ~ℓ~/ @ fid
  | M => ∃ fid ℓ, γ ~ℓ~ ℓ @ fid
  | I => True
  end.

Global Instance lstore_own_vblock_I_persistent γ dq b :
  Persistent (lstore_own_vblock γ I dq b).
Proof using.
  unfold Persistent.
  iIntros "[? _]". unfold lstore_own_elem.
  cbn. rewrite bi.persistently_sep bi.persistently_pure.
  iSplit; auto. by iApply persistent.
Qed.

Lemma lstore_own_vblock_I_as_imm γ dq b :
  lstore_own_vblock γ I dq b ⊣⊢ lstore_own_immut γ (Bvblock (Immut, b)).
Proof using.
  iSplit; unfold lstore_own_vblock; iIntros "[? _]"; by iSplit.
Qed.

Lemma lstore_own_vblock_M_as_mut γ dq b :
  lstore_own_vblock γ M dq b ⊣⊢ lstore_own_mut γ dq (Bvblock (Mut, b)) ∗ ∃ fid ℓ, γ ~ℓ~ ℓ @ fid.
Proof using.
  iSplit; unfold lstore_own_vblock.
  { iIntros "(? & H)". iDestruct "H" as (?) "?". iFrame. eauto. }
  { iIntros "[[? _] ?]". iFrame. }
Qed.

Lemma lstore_own_vblock_F_as_mut γ dq b :
  lstore_own_vblock γ F dq b ⊣⊢ lstore_own_mut γ dq (Bvblock (Mut, b)) ∗ ∃ fid, γ ~ℓ~/ @ fid.
Proof using.
  iSplit; unfold lstore_own_vblock.
  { iIntros "[? ?]". by iFrame. }
  { iIntros "[[? _] ?]". by iFrame. }
Qed.

Lemma lstore_own_vblock_mutable_as_mut γ dq acc b :
  vblock_access_le M acc →
  lstore_own_vblock γ acc dq b ⊣⊢
  lstore_own_mut γ dq (Bvblock (Mut, b)) ∗
  match acc with F => ∃ fid, γ ~ℓ~/ @ fid | M => ∃ fid ℓ, γ ~ℓ~ ℓ @ fid | I => True end.
Proof using.
  iIntros (Hacc). iSplit.
  { iIntros "[? ?]". iFrame. iSplit; eauto.
    inversion Hacc; subst; eauto. }
  { iIntros "[[? _] ?]". iFrame. inversion Hacc; subst; eauto. }
Qed.

Notation "γ ↦vblk[ a ]{ dq } b" := (lstore_own_vblock γ a dq b)
  (at level 20, format "γ  ↦vblk[ a ]{ dq }  b") : bi_scope.
Notation "γ ↦vblk[ a ] b" := (γ ↦vblk[a]{DfracOwn 1} b)%I
  (at level 20, format "γ  ↦vblk[ a ]  b") : bi_scope.

Notation "γ ↦fresh{ dq } b" := (γ ↦vblk[F]{dq} b)%I
  (at level 20, format "γ  ↦fresh{ dq }  b") : bi_scope.
Notation "γ ↦fresh b" := (γ ↦fresh{DfracOwn 1} b)%I
  (at level 20, format "γ  ↦fresh  b") : bi_scope.
Notation "γ ↦mut{ dq } b" := (γ ↦vblk[M]{dq} b)%I
  (at level 20, format "γ  ↦mut{ dq }  b") : bi_scope.
Notation "γ ↦mut b" := (γ ↦mut{DfracOwn 1} b)%I
  (at level 20, format "γ  ↦mut  b") : bi_scope.
Notation "γ ↦imm b" := (γ ↦vblk[I]{DfracOwn 1} b)%I
  (at level 20, format "γ  ↦imm  b") : bi_scope.

(* Closure points-to *)

Notation "γ ↦clos ( f , x , e )" := (lstore_own_immut γ (Bclosure f x e))%I
  (at level 20, format "γ  ↦clos  ( f ,  x ,  e )") : bi_scope.

(* Foreign block points-to *)

Definition lstore_own_foreign γ dq (v : option word) : iProp Σ :=
  lstore_own_mut γ dq (Bforeign v) ∗ ∃ id, γ ~foreign~ id.


Notation "γ ↦foreignO{ dq } a" := (lstore_own_foreign γ dq a)%I
  (at level 20, format "γ  ↦foreignO{ dq }  a") : bi_scope.
Notation "γ ↦foreignO a" := (γ ↦foreignO{DfracOwn 1} a)%I
  (at level 20, format "γ  ↦foreignO  a") : bi_scope.

(* Lifting of ~ℓ~ at the level of ML values *)

Fixpoint block_sim (v : val) (l : lval) : iProp Σ := match v with
  | ML_lang.LitV (ML_lang.LitInt x) => ⌜l = (Lint x)⌝
  | ML_lang.LitV (ML_lang.LitBool b) => ⌜l = (Lint (if b then 1 else 0))⌝
  | ML_lang.LitV ML_lang.LitUnit => ⌜l = (Lint 0)⌝
  | ML_lang.LitV (ML_lang.LitLoc ℓ) => ∃ γ fid, ⌜l = (Lloc γ)⌝ ∗ γ ~ℓ~ ℓ @ fid
  | ML_lang.LitV (ML_lang.LitForeign id) => ∃ γ, ⌜l = (Lloc γ)⌝ ∗ γ ~@~ id
  | ML_lang.PairV v1 v2 => ∃ γ lv1 lv2,
      ⌜l = (Lloc γ)⌝ ∗
      γ ↦imm (TagDefault, [lv1;lv2]) ∗
      block_sim v1 lv1 ∗ block_sim v2 lv2
  | ML_lang.InjLV v => ∃ γ lv,
      ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (TagDefault, [lv]) ∗ block_sim v lv
  | ML_lang.InjRV v => ∃ γ lv,
      ⌜l = (Lloc γ)⌝ ∗ γ ↦imm (TagInjRV, [lv]) ∗ block_sim v lv
  | ML_lang.RecV f x e => ∃ γ,
      ⌜l = Lloc γ⌝ ∗ γ ↦clos (f, x, e)
end.

Notation "lv  ~~  v" := (block_sim v lv) (at level 20).

Global Instance block_sim_pers v l : Persistent (l ~~ v).
Proof using.
  induction v as [[x|b| | |]| | | |] in l|-*; cbn; unshelve eapply (_).
Qed.

Definition block_sim_arr (vs:list ML_lang.val) (ls : list lval) : iProp Σ :=
  [∗ list] v;l ∈ vs;ls, l ~~ v.

Notation "lvs  ~~∗  vs" := (block_sim_arr vs lvs) (at level 20).

Lemma block_sim_of_auth (ζfreeze ζσ ζvirt : lstore) (χvirt : lloc_map) (σMLvirt : store)
   v b :
  ζfreeze = ζσ ∪ ζvirt →
  is_store_blocks χvirt σMLvirt ζσ →
  is_store χvirt ζfreeze σMLvirt →
  ζσ ##ₘ ζvirt →
  is_val χvirt ζfreeze v b →
  lloc_own_auth χvirt -∗
  lstore_own_auth ζvirt -∗
  b ~~ v.
Proof using.
  iIntros (Hfreeze Hstorebl Hstore Hdisj H) "Hχ Hζ".
  iDestruct (lstore_own_auth_get_immut_all with "Hζ") as "#Hζimm".
  iInduction H as [] "IH" forall "Hζ Hχ"; cbn; try done.
  1: iExists γ, fid; iSplit; first done.
  1: by iApply (lloc_own_auth_get_pub with "Hχ").
  1: iExists γ, lv1, lv2; iSplit; first done; iSplit.
  3-4: iExists γ, lv; iSplit; first done; iSplit.
  7: iExists γ; iSplit; first done.
  8: iExists γ; iSplit; first done.
  8: simplify_eq; by iApply (lloc_own_auth_get_fid with "Hχ").
  1,3,5,7:
    try iApply lstore_own_vblock_I_as_imm;
    iApply (big_sepM_lookup with "Hζimm"); try done.
  5: iSplit.
  5,7,8: by iApply ("IH" with "[] [] [] Hζ Hχ").
  5: by iApply ("IH1" with "[] [] [] Hζ Hχ").
  all: simplify_eq.
  all: apply lstore_immut_blocks_lookup_immut.
  all: match goal with H: (_ ∪ _) !! _ = Some _ |- _ =>
      apply lookup_union_Some in H as [|]; eauto end.
  all: destruct Hstorebl as [_ Hstorebl2].
  all: specialize (Hstorebl2 γ) as [Hstorebl2 _].
  all: destruct Hstorebl2 as (fid & ℓ & Vs & Hχ & Hσml); [by eapply elem_of_dom_2|].
  all: efeed specialize Hstore; eauto; [eapply lookup_union_Some; by eauto|].
  all: inversion Hstore.
Qed.

Lemma block_sim_of_auth_strong (ζfreeze : lstore) (χvirt : lloc_map)
   v b :
  is_val χvirt ζfreeze v b →
  lloc_own_auth χvirt -∗
  lstore_own_auth ζfreeze -∗
  b ~~ v.
Proof using.
  iIntros (H) "Hχ Hζ".
  iDestruct (lstore_own_auth_get_immut_all with "Hζ") as "#Hζimm".
  iInduction H as [] "IH" forall "Hζ Hχ"; cbn; try done.
  1: iExists γ, fid; iSplit; first done.
  1: by iApply (lloc_own_auth_get_pub with "Hχ").
  1: iExists γ, lv1, lv2; iSplit; first done; iSplit.
  3-4: iExists γ, lv; iSplit; first done; iSplit.
  7: iExists γ; iSplit; first done.
  8: iExists γ; iSplit; first done.
  8: simplify_eq; by iApply (lloc_own_auth_get_fid with "Hχ").
  1,3,5,7:
    try iApply lstore_own_vblock_I_as_imm;
    iApply (big_sepM_lookup with "Hζimm"); try done.
  5: iSplit.
  1-4: apply lstore_immut_blocks_lookup_immut; done.
  1,3,4: iApply ("IH" with "Hζ Hχ").
  iApply ("IH1" with "Hζ Hχ").
Qed.

Lemma block_sim_arr_of_auth (ζfreeze ζσ ζvirt : lstore) (χvirt : lloc_map) (σMLvirt : store)
   vs bb :
  ζfreeze = ζσ ∪ ζvirt →
  is_store_blocks χvirt σMLvirt ζσ →
  is_store χvirt ζfreeze σMLvirt →
  ζσ ##ₘ ζvirt →
  Forall2 (is_val χvirt ζfreeze) vs bb →
  lloc_own_auth χvirt -∗
  lstore_own_auth ζvirt -∗
  bb ~~∗ vs.
Proof using.
  iIntros (Hfreeze Hstorebl Hstore Hdisj H) "Hχ Hζ".
  iApply big_sepL2_forall; iSplit; first (iPureIntro; by eapply Forall2_length).
  iIntros "%k %v %l %H1 %H2".
  iApply (block_sim_of_auth with "Hχ Hζ"); try done.
  eapply Forall2_lookup_lr; done.
Qed.

Lemma block_sim_arr_of_auth_strong (ζfreeze : lstore) (χvirt : lloc_map)
   vs bb :
  Forall2 (is_val χvirt ζfreeze) vs bb →
  lloc_own_auth χvirt -∗
  lstore_own_auth ζfreeze -∗
  bb ~~∗ vs.
Proof using.
  iIntros (H) "Hχ Hζ".
  iApply big_sepL2_forall; iSplit; first (iPureIntro; by eapply Forall2_length).
  iIntros "%k %v %l %H1 %H2".
  iApply (block_sim_of_auth_strong with "Hχ Hζ"); try done.
  eapply Forall2_lookup_lr; done.
Qed. 

Lemma block_sim_auth_is_val_strong  (ζfreeze ζσ ζvirt ζplus : lstore) (χvirt : lloc_map)
   v b :
  ζfreeze = ζσ ∪ ζvirt →
  ζσ ##ₘ ζvirt →
  lloc_own_auth χvirt -∗
  lstore_own_auth (ζplus ∪ ζvirt) -∗
  ([∗ map] γ↦b ∈ ζplus, pgm_elem (D:=LstorePGMData) wrapperG_γζvirt γ (DfracOwn 1) b) -∗
  b ~~ v -∗
  ⌜is_val χvirt ζfreeze v b⌝.
Proof using.
  iIntros (Hfreeze Hdis) "Hχ Hζ Hplus Hsim".
  iInduction v as [[x|bo| | |]| | | |] "IH" forall (b); cbn.
  all: try (iPure "Hsim" as Hsim; subst; iPureIntro; try econstructor; done).
  1: {iDestruct "Hsim" as "(%γ & %fid & -> & Hsim)".
      iPoseProof (lloc_own_pub_of with "Hχ Hsim") as "%HH".
      iPureIntro. econstructor. done. }
  1: { iDestruct "Hsim" as "(%γ & -> & Hsim)".
       iDestruct (lloc_own_pers_of with "Hχ Hsim") as %(vis&Heq1&Heq2).
       iPureIntro. econstructor; done. }
  1: iDestruct "Hsim" as "(%γ & -> & Hsim)".
  2: iDestruct "Hsim" as "(%γ & %lv1 & %lv2 & -> & Hsim & Hlv1 & Hlv2)";
     iPoseProof ("IH" with "Hχ Hζ Hplus Hlv1") as "%Hr1";
     iPoseProof ("IH1" with "Hχ Hζ Hplus Hlv2") as "%Hr2".
  3-4: iDestruct "Hsim" as "(%γ & %lv & -> & Hsim & Hlv)";
       iPoseProof ("IH" with "Hχ Hζ Hplus Hlv") as "%Hr".
  all: try iDestruct (lstore_own_vblock_I_as_imm with "Hsim") as "Hsim".
  1-4: unshelve iPoseProof (lstore_own_immut_of with "Hζ Hsim") as "#[%HH _]".
  all: eapply lookup_union_Some_raw in HH as [HH|(Hne&HH)]; last
       (iDestruct "Hsim" as "(Hsim&_)"; rewrite /lstore_own_immut; try iDestruct "Hsim" as "(Hsim&_)").
  1: iPoseProof (lstore_own_immut_to_elem with "Hsim") as "Hsim";
     iPoseProof (big_sepM_lookup_acc with "Hplus") as "(Hcontr&_)"; first done;
     cbn; iPoseProof (pgm_elem_ne with "Hcontr Hsim") as "%HH2"; done.
  2: iPoseProof (lstore_own_immut_to_elem with "Hsim") as "Hsim";
     iPoseProof (big_sepM_lookup_acc with "Hplus") as "(Hcontr&_)"; first done;
     cbn; iPoseProof (pgm_elem_ne with "Hcontr Hsim") as "%HH2"; done.
  3: iPoseProof (lstore_own_immut_to_elem with "Hsim") as "Hsim";
     iPoseProof (big_sepM_lookup_acc with "Hplus") as "(Hcontr&_)"; first done;
     cbn; iPoseProof (pgm_elem_ne with "Hcontr Hsim") as "%HH2"; done.
  4: iPoseProof (lstore_own_immut_to_elem with "Hsim") as "Hsim";
     iPoseProof (big_sepM_lookup_acc with "Hplus") as "(Hcontr&_)"; first done;
     cbn; iPoseProof (pgm_elem_ne with "Hcontr Hsim") as "%HH2"; done.
  all: iPureIntro; econstructor; eauto; by simplify_map_eq.
Qed.

Lemma block_sim_auth_is_val  (ζfreeze ζσ ζvirt : lstore) (χvirt : lloc_map)
   v b :
  ζfreeze = ζσ ∪ ζvirt →
  ζσ ##ₘ ζvirt →
  lloc_own_auth χvirt -∗
  lstore_own_auth ζvirt -∗
  b ~~ v -∗
  ⌜is_val χvirt ζfreeze v b⌝.
Proof using.
  iIntros (Hfreeze Hdis) "Hχ Hζ Hsim".
  iApply (block_sim_auth_is_val_strong _ _ _ ∅ with "Hχ [Hζ] [] Hsim").
  - apply Hfreeze.
  - apply Hdis.
  - by rewrite map_empty_union.
  - done.
Qed.

Lemma block_sim_auth_is_val_simple (ζfreeze : lstore) (χvirt : lloc_map)
   v b :
  lloc_own_auth χvirt -∗
  lstore_own_auth ζfreeze -∗
  b ~~ v -∗
  ⌜is_val χvirt ζfreeze v b⌝.
Proof using.
  iIntros "Hχ Hζ Hsim".
  iApply (block_sim_auth_is_val _ ∅ _ with "Hχ Hζ Hsim").
  - by rewrite map_empty_union.
  - eapply map_disjoint_empty_l.
Qed.

Lemma block_sim_arr_auth_is_val_strong (ζfreeze ζσ ζvirt ζplus : lstore) (χvirt : lloc_map)
   vs bb :
  ζfreeze = ζσ ∪ ζvirt →
  ζσ ##ₘ ζvirt →
  lloc_own_auth χvirt -∗
  lstore_own_auth (ζplus ∪ ζvirt) -∗
  ([∗ map] γ↦b ∈ ζplus, pgm_elem (D:=LstorePGMData) wrapperG_γζvirt γ (DfracOwn 1) b) -∗
  bb ~~∗ vs -∗
  ⌜Forall2 (is_val χvirt ζfreeze) vs bb⌝.
Proof using.
  iIntros (Hfreeze Hdis) "Hχ Hζ Hplus Hsim".
  iPoseProof (big_sepL2_forall with "Hsim") as "(%Heq & Hsim)".
  iAssert (⌜(∀ i x y, vs !! i = Some x → bb !! i = Some y → is_val χvirt ζfreeze x y)⌝)%I as "%HF".
  2: iPureIntro; by apply Forall2_same_length_lookup_2.
  iIntros (i v b H1 H2).
  iApply (block_sim_auth_is_val_strong with "Hχ Hζ Hplus"); try done.
  iApply ("Hsim" $! i v b H1 H2).
Qed.

Lemma block_sim_arr_auth_is_val (ζfreeze ζσ ζvirt : lstore) (χvirt : lloc_map)
   vs bb :
  ζfreeze = ζσ ∪ ζvirt →
  ζσ ##ₘ ζvirt →
  lloc_own_auth χvirt -∗
  lstore_own_auth ζvirt -∗
  bb ~~∗ vs -∗
  ⌜Forall2 (is_val χvirt ζfreeze) vs bb⌝.
Proof using.
  iIntros (Hfreeze Hdis) "Hχ Hζ Hsim".
  iApply (block_sim_arr_auth_is_val_strong _ _ _ ∅ with "Hχ [Hζ] [] Hsim").
  - apply Hfreeze.
  - apply Hdis.
  - by rewrite map_empty_union.
  - done.
Qed.

Lemma block_sim_arr_auth_is_val_simple (ζfreeze : lstore) (χvirt : lloc_map)
   vs bb :
  lloc_own_auth χvirt -∗
  lstore_own_auth ζfreeze -∗
  bb ~~∗ vs -∗
  ⌜Forall2 (is_val χvirt ζfreeze) vs bb⌝.
Proof using.
  iIntros "Hχ Hζ Hsim".
  iApply (block_sim_arr_auth_is_val _ ∅ _ with "Hχ Hζ Hsim").
  - by rewrite map_empty_union.
  - eapply map_disjoint_empty_l.
Qed.


End BasicsResources.

Global Hint Constructors vblock_access_le : core.

(* Re-export notations *)

Notation "γ ~ℓ~ ℓ @ fid" := (lloc_own_pub γ fid ℓ)
  (at level 20, format "γ  ~ℓ~  ℓ  @  fid").
Notation "γ ~ℓ~/ @ fid" := (lloc_own_priv (DfracOwn 1) γ fid)
  (at level 20, format "γ  ~ℓ~/  @  fid").
Notation "γ ~ℓ~/{ dq } @ fid" := (lloc_own_priv dq γ fid)
  (at level 20, format "γ  ~ℓ~/{ dq }  @  fid").
Notation "γ ~foreign~ id" := (lloc_own_foreign γ id)
  (at level 20, format "γ  ~foreign~  id").
Notation "γ ~@~ id" := (lloc_own_fid γ id)
  (at level 20, format "γ  ~@~  id").

Notation "lv  ~~  v" := (block_sim v lv) (at level 20).
Notation "lvs  ~~∗  vs" := (block_sim_arr vs lvs) (at level 20).

Notation "γ ↦vblk[ a ]{ dq } b" := (lstore_own_vblock γ a dq b)
  (at level 20, format "γ  ↦vblk[ a ]{ dq }  b") : bi_scope.
Notation "γ ↦vblk[ a ] b" := (γ ↦vblk[a]{DfracOwn 1} b)%I
  (at level 20, format "γ  ↦vblk[ a ]  b") : bi_scope.

Notation "γ ↦fresh{ dq } b" := (γ ↦vblk[F]{dq} b)%I
  (at level 20, format "γ  ↦fresh{ dq }  b") : bi_scope.
Notation "γ ↦fresh b" := (γ ↦fresh{DfracOwn 1} b)%I
  (at level 20, format "γ  ↦fresh  b") : bi_scope.
Notation "γ ↦mut{ dq } b" := (γ ↦vblk[M]{dq} b)%I
  (at level 20, format "γ  ↦mut{ dq }  b") : bi_scope.
Notation "γ ↦mut b" := (γ ↦mut{DfracOwn 1} b)%I
  (at level 20, format "γ  ↦mut  b") : bi_scope.
Notation "γ ↦imm b" := (γ ↦vblk[I]{DfracOwn 1} b)%I
  (at level 20, format "γ  ↦imm  b") : bi_scope.

Notation "γ ↦head h" := (lstore_own_head γ h)
  (at level 20, format "γ  ↦head  h") : bi_scope.

Notation "γ ↦clos ( f , x , e )" := (lstore_own_immut γ (Bclosure f x e))%I
  (at level 20, format "γ  ↦clos  ( f ,  x ,  e )") : bi_scope.

Notation "γ ↦foreignO{ dq } a" := (lstore_own_foreign γ dq a)%I
  (at level 20, format "γ  ↦foreignO{ dq }  a") : bi_scope.
Notation "γ ↦foreignO a" := (γ ↦foreignO{DfracOwn 1} a)%I
  (at level 20, format "γ  ↦foreignO  a") : bi_scope.
Notation "γ ↦foreign{ dq } a" := (γ ↦foreignO{ dq } (Some a))%I
  (at level 20, format "γ  ↦foreign{ dq }  a") : bi_scope.
Notation "γ ↦foreign a" := (γ ↦foreign{DfracOwn 1} a)%I
  (at level 20, format "γ  ↦foreign  a") : bi_scope.

Notation "γ ↦roots{ dq } w" := (γ ↪[wrapperG_γroots_map]{dq} w)%I
  (at level 20, format "γ  ↦roots{ dq }  w") : bi_scope.
Notation "γ ↦roots w" := (γ ↪[wrapperG_γroots_map] w)%I
  (at level 20, format "γ  ↦roots  w") : bi_scope.
