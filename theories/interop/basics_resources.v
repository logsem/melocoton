From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From iris.base_logic.lib Require Import ghost_map ghost_var gen_heap.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props.
From melocoton.interop Require Export basics.

Class wrapperBasicsGS Σ := WrapperBasicsGS {
  wrapperGS_lstoreGS :> ghost_mapG Σ lloc block;
  wrapperGS_addr_lvalGS :> ghost_mapG Σ addr lval;
  wrapperGS_lloc_mapGS :> ghost_mapG Σ lloc lloc_visibility;
  wrapperGS_γζvirt : gname;
  wrapperGS_γχvirt : gname;
  wrapperGS_γroots_map : gname;
}.

Section BasicsResources.
Context `{!wrapperBasicsGS Σ}.

(* Ghost state for [lloc_map] *)

Definition lloc_own_priv (γ : lloc) : iProp Σ :=
  γ ↪[wrapperGS_γχvirt] LlocPrivate.

Definition lloc_own_pub (γ : lloc) (ℓ : loc) : iProp Σ :=
  γ ↪[wrapperGS_γχvirt]□ LlocPublic ℓ.

Instance lloc_own_pub_persistent γ ℓ : Persistent (lloc_own_pub γ ℓ).
Proof using. apply _. Qed.

Definition lloc_own_auth (χ : lloc_map) : iProp Σ :=
  "Hχgmap" ∷ ghost_map_auth wrapperGS_γχvirt 1 χ ∗
  "Hχpubs" ∷ ([∗ map] γ↦ℓ ∈ (lloc_map_pubs χ), lloc_own_pub γ ℓ).

(* FIXME: aliased name *)
(* TODO: custom notation (like l1 ~~ML l2 )? *)
(* l1 is a location in the ML heap. l2 is a block location.
   They are similar if identified by χ *)
Definition block_sim_raw (ℓ : loc) (γ : lloc) : iProp Σ :=
  lloc_own_pub γ ℓ.

Lemma lloc_own_auth_get_pub_all χ :
  lloc_own_auth χ -∗
  [∗ map] γ↦ℓ ∈ (lloc_map_pubs χ), lloc_own_pub γ ℓ.
Proof using.
  iNamed 1. iApply "Hχpubs".
Qed.

Lemma lloc_own_auth_get_pub χ γ ℓ :
  χ !! γ = Some (LlocPublic ℓ) →
  lloc_own_auth χ -∗
  lloc_own_pub γ ℓ.
Proof using.
  intros Hγ. iNamed 1.
  iDestruct (big_sepM_lookup with "Hχpubs") as "?"; eauto.
Qed.

Lemma lloc_own_pub_of χ γ ℓ :
  lloc_own_auth χ -∗
  lloc_own_pub γ ℓ -∗
  ⌜χ !! γ = Some (LlocPublic ℓ)⌝.
Proof using.
  iIntros "Hχ Hpub". iNamed "Hχ".
  by iDestruct (ghost_map_lookup with "Hχgmap Hpub") as %?.
Qed.

Lemma lloc_own_priv_of χ γ :
  lloc_own_auth χ -∗
  lloc_own_priv γ -∗
  ⌜χ !! γ = Some LlocPrivate⌝.
Proof using.
  iIntros "Hχ Hpub". iNamed "Hχ".
  by iDestruct (ghost_map_lookup with "Hχgmap Hpub") as %?.
Qed.

Lemma lloc_own_expose χ γ ℓ :
  lloc_own_auth χ -∗
  lloc_own_priv γ ==∗
  lloc_own_auth (<[γ:=LlocPublic ℓ]> χ) ∗ lloc_own_pub γ ℓ.
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

Lemma lloc_own_allocate χ γ:
  ⌜χ !! γ = None⌝     -∗
  lloc_own_auth χ ==∗
  lloc_own_auth (<[γ:=LlocPrivate]> χ) ∗ lloc_own_priv γ.
Proof using.
  iIntros (Hne) "Hχ".
  iNamed "Hχ".
  iMod (ghost_map_insert with "Hχgmap") as "[Hχmap Hγ]"; first done.
  iModIntro. iSplitR "Hγ"; last done.
  iSplitL "Hχmap"; first done. unfold named.
  rewrite lloc_map_pubs_insert_priv delete_notin.
  2: destruct (lloc_map_pubs χ !! γ) eqn:Heq; try done; apply lloc_map_pubs_lookup_Some in Heq; congruence.
  done.
Qed.

Lemma lloc_own_insert χ γ v:
  ⌜χ !! γ = None⌝     -∗
  lloc_own_auth χ ==∗
  lloc_own_auth (<[γ:=v]> χ).
Proof using.
  iIntros (Hne) "Hχ".
  iMod (lloc_own_allocate with "[] Hχ") as "(Hχ & Hγp)"; first done.
  destruct v as [l|]; last by iModIntro.
  iMod (lloc_own_expose with "Hχ Hγp") as "(H & _)". rewrite insert_insert; done.
Qed.

Lemma lloc_own_mono χ1 χ2 :
  lloc_map_mono χ1 χ2  →
  lloc_own_auth χ1 ==∗
  lloc_own_auth χ2.
Proof.
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
  1: intros i v1 v2 H1 H2; eapply Hinj; (erewrite lookup_insert_ne; first done); intros <-.
  1-2: apply elem_of_dom_2 in H1,H2; eapply not_elem_of_dom in Hne,Hnone; rewrite dom_union_L in H1,H2; set_solver.
  1: done.
  1: done.
  rewrite <- insert_union_r; last done.
  iMod (lloc_own_insert with "[] Hown") as "$"; last done.
  iPureIntro; apply lookup_union_None; done.
Qed.

(* Ghost state for [lstore] *)

Definition lstore_own_elem (γ : lloc) (dq : dfrac) (b : block) :=
  match mutability b with
  | Mut => γ ↪[wrapperGS_γζvirt]{dq} b
  | Immut => γ ↪[wrapperGS_γζvirt]□ b
  end%I.

Definition lstore_own_mut (γ : lloc) (dq : dfrac) (b : block) :=
  (lstore_own_elem γ dq b ∗ ⌜mutability b = Mut⌝)%I.

Definition lstore_own_immut (γ : lloc) (b : block) :=
  (lstore_own_elem γ (DfracOwn 1) b ∗ ⌜mutability b = Immut⌝)%I.

Definition lstore_own_auth (ζ : lstore) : iProp Σ :=
  "Hζgmap" ∷ ghost_map_auth wrapperGS_γζvirt 1 ζ ∗
  "#Hζimmut" ∷ ([∗ map] γ↦b ∈ (lstore_immut_blocks ζ), lstore_own_immut γ b).

Global Instance lstore_own_immut_persistent γ b :
  Persistent (lstore_own_immut γ b).
Proof using.
  unfold Persistent.
  iIntros "[? %H]". unfold lstore_own_immut, lstore_own_elem.
  rewrite H. rewrite bi.persistently_sep bi.persistently_pure.
  iSplit; auto. by iApply persistent.
Qed.

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
    by iDestruct (ghost_map_lookup with "Hζgmap He") as "?".
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

Lemma lstore_own_insert ζ γ b :
  ζ !! γ = None →
  lstore_own_auth ζ ==∗
  lstore_own_auth (<[γ:=b]> ζ) ∗ lstore_own_elem γ (DfracOwn 1) b.
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
  lstore_own_auth ζ -∗
  lstore_own_mut γ (DfracOwn 1) b ==∗
  lstore_own_auth (<[γ:=b']> ζ) ∗ lstore_own_elem γ (DfracOwn 1) b'.
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

Lemma lstore_own_delete ζ γ b :
  lstore_own_auth ζ -∗
  lstore_own_mut γ (DfracOwn 1) b ==∗
  lstore_own_auth (delete γ ζ).
Proof using.
  iNamed 1. iIntros "[He %Hmut]". rewrite /lstore_own_elem Hmut.
  iMod (ghost_map_delete with "Hζgmap He") as "Hζgmap". iFrame.
  rewrite lstore_immut_blocks_delete.
  iApply (big_sepM_subseteq with "Hζimmut"). apply delete_subseteq.
Qed.

End BasicsResources.

Notation "l ↦fresh{ dq } b" := (lstore_own_mut l dq (Bvblock (Mut, b)) ∗ lloc_own_priv l)%I
  (at level 20, format "l  ↦fresh{ dq }  b") : bi_scope.
Notation "l ↦fresh b" := (l ↦fresh{DfracOwn 1} b)%I
  (at level 20, format "l  ↦fresh  b") : bi_scope.
Notation "l ↦mut{ dq } b" := (lstore_own_mut l dq (Bvblock (Mut, b)) ∗ ∃ ll, block_sim_raw ll l)%I
  (at level 20, format "l  ↦mut{ dq }  b") : bi_scope.
Notation "l ↦mut b" := (l ↦mut{DfracOwn 1} b)%I
  (at level 20, format "l  ↦mut  b") : bi_scope.
Notation "l ↦imm b" := (lstore_own_immut l (Bvblock (Immut, b)))%I
  (at level 20, format "l  ↦imm  b") : bi_scope.
Notation "l ↦roots{ dq } w" := (l ↪[wrapperGS_γroots_map]{dq} w)%I
  (at level 20, format "l  ↦roots{ dq }  w") : bi_scope.
Notation "l ↦roots w" := (l ↪[wrapperGS_γroots_map] w)%I
  (at level 20, format "l  ↦roots  w") : bi_scope.
Notation "l ↦clos ( f , x , e )" := (lstore_own_immut l (Bclosure f x e))%I
  (at level 20, format "l  ↦clos  ( f ,  x ,  e )").
