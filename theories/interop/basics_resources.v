From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props.
From melocoton.interop Require Export basics.

Section BasicsResources.
Context {Σ : gFunctors}.
Context {llocmapGS: ghost_mapG Σ lloc lloc_visibility}.
Context {lstoreGS: ghost_mapG Σ lloc block}.

(* Ghost state for [lloc_map] *)

Definition lloc_own_priv (γGS : gname) (γ : lloc) : iProp Σ :=
  γ ↪[γGS] LlocPrivate.

Definition lloc_own_pub (γGS : gname) (γ : lloc) (ℓ : loc) : iProp Σ :=
  γ ↪[γGS]□ LlocPublic ℓ.

Instance lloc_own_pub_persistent γGS γ ℓ : Persistent (lloc_own_pub γGS γ ℓ).
Proof using. apply _. Qed.

Definition lloc_own_auth (γGS : gname) (χ : lloc_map) : iProp Σ :=
  "Hχgmap" ∷ ghost_map_auth γGS 1 χ ∗
  "Hχpubs" ∷ ([∗ map] γ↦ℓ ∈ (lloc_map_pubs χ), lloc_own_pub γGS γ ℓ).

Lemma lloc_own_auth_get_pub_all γGS χ :
  lloc_own_auth γGS χ -∗
  [∗ map] γ↦ℓ ∈ (lloc_map_pubs χ), lloc_own_pub γGS γ ℓ.
Proof using.
  iNamed 1. iApply "Hχpubs".
Qed.

Lemma lloc_own_auth_get_pub γGS χ γ ℓ :
  χ !! γ = Some (LlocPublic ℓ) →
  lloc_own_auth γGS χ -∗
  lloc_own_pub γGS γ ℓ.
Proof using.
  intros Hγ. iNamed 1.
  iDestruct (big_sepM_lookup with "Hχpubs") as "?"; eauto.
Qed.

Lemma lloc_own_pub_of γGS χ γ ℓ :
  lloc_own_auth γGS χ -∗
  lloc_own_pub γGS γ ℓ -∗
  ⌜χ !! γ = Some (LlocPublic ℓ)⌝.
Proof using.
  iIntros "Hχ Hpub". iNamed "Hχ".
  by iDestruct (ghost_map_lookup with "Hχgmap Hpub") as %?.
Qed.

Lemma lloc_own_priv_of γGS χ γ :
  lloc_own_auth γGS χ -∗
  lloc_own_priv γGS γ -∗
  ⌜χ !! γ = Some LlocPrivate⌝.
Proof using.
  iIntros "Hχ Hpub". iNamed "Hχ".
  by iDestruct (ghost_map_lookup with "Hχgmap Hpub") as %?.
Qed.

Lemma lloc_own_expose γGS χ γ ℓ :
  lloc_own_auth γGS χ -∗
  lloc_own_priv γGS γ ==∗
  lloc_own_auth γGS (<[γ:=LlocPublic ℓ]> χ) ∗ lloc_own_pub γGS γ ℓ.
Proof using.
  iIntros "Hχ Hγ".
  iDestruct (lloc_own_priv_of with "Hχ Hγ") as %Hχγ.
  iNamed "Hχ".
  iMod (ghost_map_update with "Hχgmap Hγ") as "[$ Hγ]".
  iMod (ghost_map_elem_persist with "Hγ") as "#Hγ".
  iFrame "Hγ". iModIntro.
  rewrite lloc_map_pubs_insert_pub.
  iApply big_sepM_insert; eauto.
  apply lloc_map_pubs_lookup_None; eauto.
Qed.

(* Ghost state for [lstore] *)

Definition lstore_own_elem (γGS : gname) (γ : lloc) (dq : dfrac) (b : block) :=
  match mutability b with
  | Mut => γ ↪[γGS]{dq} b
  | Immut => γ ↪[γGS]□ b
  end%I.

Definition lstore_own_mut (γGS : gname) (γ : lloc) (dq : dfrac) (b : block) :=
  (lstore_own_elem γGS γ dq b ∗ ⌜mutability b = Mut⌝)%I.

Definition lstore_own_immut (γGS : gname) (γ : lloc) (b : block) :=
  (lstore_own_elem γGS γ (DfracOwn 1) b ∗ ⌜mutability b = Immut⌝)%I.

Definition lstore_own_auth (γGS : gname) (ζ : lstore) : iProp Σ :=
  "Hζgmap" ∷ ghost_map_auth γGS 1 ζ ∗
  "#Hζimmut" ∷ ([∗ map] γ↦b ∈ (lstore_immut_blocks ζ), lstore_own_immut γGS γ b).

Global Instance lstore_own_immut_persistent γGS γ b :
  Persistent (lstore_own_immut γGS γ b).
Proof using.
  unfold Persistent.
  iIntros "[? %H]". unfold lstore_own_immut, lstore_own_elem.
  rewrite H. rewrite bi.persistently_sep bi.persistently_pure.
  iSplit; auto. by iApply persistent.
Qed.

Lemma lstore_own_elem_to_mut γGS γ dq b :
  mutability b = Mut →
  lstore_own_elem γGS γ dq b -∗
  lstore_own_mut γGS γ dq b.
Proof using. intros H. rewrite /lstore_own_mut /lstore_own_elem H. eauto. Qed.

Lemma lstore_own_mut_to_elem γGS γ dq b :
  lstore_own_mut γGS γ dq b -∗
  lstore_own_elem γGS γ dq b.
Proof using. by iIntros "[? _]". Qed.

Lemma lstore_own_elem_to_immut γGS γ dq b :
  mutability b = Immut →
  lstore_own_elem γGS γ dq b -∗
  lstore_own_immut γGS γ b.
Proof using. intros H. rewrite /lstore_own_immut /lstore_own_elem H. eauto. Qed.

Lemma lstore_own_immut_to_elem γGS γ b :
  lstore_own_immut γGS γ b -∗
  lstore_own_elem γGS γ (DfracOwn 1) b.
Proof using. by iIntros "[? _]". Qed.

Lemma lstore_own_auth_get_immut_all γGS ζ :
  lstore_own_auth γGS ζ -∗
  [∗ map] γ↦b ∈ (lstore_immut_blocks ζ), lstore_own_immut γGS γ b.
Proof using.
  iNamed 1. iApply "Hζimmut".
Qed.

Lemma lstore_own_auth_get_immut γGS ζ γ b :
  ζ !! γ = Some b →
  mutability b = Immut →
  lstore_own_auth γGS ζ -∗
  lstore_own_immut γGS γ b.
Proof using.
  intros ? ?. iNamed 1.
  iDestruct (big_sepM_lookup with "Hζimmut") as "?"; eauto.
  by eapply lstore_immut_blocks_lookup_immut.
Qed.

Lemma lstore_own_elem_of γGS ζ γ dq b :
  lstore_own_auth γGS ζ -∗
  lstore_own_elem γGS γ dq b -∗
  ⌜ζ !! γ = Some b⌝.
Proof using.
  iNamed 1. iIntros "He".
  destruct (mutability b) eqn:Hmut; rewrite /lstore_own_elem Hmut;
    by iDestruct (ghost_map_lookup with "Hζgmap He") as %?.
Qed.

Lemma lstore_own_mut_of γGS ζ γ dq b :
  lstore_own_auth γGS ζ -∗
  lstore_own_mut γGS γ dq b -∗
  ⌜ζ !! γ = Some b ∧ mutability b = Mut⌝.
Proof using.
  iIntros "Ha [H %]".
  by iDestruct (lstore_own_elem_of with "Ha H") as %?.
Qed.

Lemma lstore_own_immut_of γGS ζ γ b :
  lstore_own_auth γGS ζ -∗
  lstore_own_immut γGS γ b -∗
  ⌜ζ !! γ = Some b ∧ mutability b = Immut⌝.
Proof using.
  iIntros "Ha [H %]".
  by iDestruct (lstore_own_elem_of with "Ha H") as %?.
Qed.

Lemma lstore_own_insert γGS ζ γ b :
  ζ !! γ = None →
  lstore_own_auth γGS ζ ==∗
  lstore_own_auth γGS (<[γ:=b]> ζ) ∗ lstore_own_elem γGS γ (DfracOwn 1) b.
Proof using.
  iIntros (Hγ). iNamed 1.
  iMod (ghost_map_insert _ b with "Hζgmap") as "[Hζgmap Helt]"; eauto.
  iFrame "Hζgmap".
  destruct (mutability b) eqn:Hmut.
  { rewrite /lstore_own_elem Hmut. iFrame "Helt".
    rewrite lstore_immut_blocks_insert_mut // delete_notin //; eauto. }
  { iMod (ghost_map_elem_persist with "Helt") as "#Helt".
    rewrite /lstore_own_elem Hmut. iFrame "Helt".
    iModIntro. rewrite lstore_immut_blocks_insert_immut // big_sepM_insert; eauto.
    iFrame. rewrite /lstore_own_immut /lstore_own_elem Hmut //. eauto. }
Qed.

Lemma lstore_own_update γGS ζ γ b b' :
  lstore_own_auth γGS ζ -∗
  lstore_own_mut γGS γ (DfracOwn 1) b ==∗
  lstore_own_auth γGS (<[γ:=b']> ζ) ∗ lstore_own_elem γGS γ (DfracOwn 1) b'.
Proof using.
  iIntros "Ha He". iDestruct (lstore_own_mut_of with "Ha He") as %[? _].
  iNamed "Ha". iDestruct "He" as "[He %Hmut]".
  rewrite /lstore_own_elem Hmut.
  iMod (ghost_map_update with "Hζgmap He") as "[Hζgmap He]".
  destruct (mutability b') eqn:Hmut'.
  { iFrame. iApply (big_sepM_subseteq with "Hζimmut").
    rewrite lstore_immut_blocks_insert_mut //. apply delete_subseteq. }
  { iMod (ghost_map_elem_persist with "He") as "#$". iFrame.
    rewrite lstore_immut_blocks_insert_immut //.
    iApply big_sepM_insert; eauto. iModIntro.
    rewrite /lstore_own_immut /lstore_own_elem Hmut'; eauto. }
Qed.

Lemma lstore_own_delete γGS ζ γ b :
  lstore_own_auth γGS ζ -∗
  lstore_own_mut γGS γ (DfracOwn 1) b ==∗
  lstore_own_auth γGS (delete γ ζ).
Proof using.
  iNamed 1. iIntros "[He %Hmut]". rewrite /lstore_own_elem Hmut.
  iMod (ghost_map_delete with "Hζgmap He") as "Hζgmap". iFrame.
  rewrite lstore_immut_blocks_delete.
  iApply (big_sepM_subseteq with "Hζimmut"). apply delete_subseteq.
Qed.

End BasicsResources.
