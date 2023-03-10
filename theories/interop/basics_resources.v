From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From iris.base_logic.lib Require Import ghost_map ghost_var gen_heap.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton Require Import named_props.
From melocoton.ml_lang Require Import lang.
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

Definition lloc_own_foreign (γ : lloc) (id : nat) : iProp Σ :=
  γ ↪[wrapperGS_γχvirt]□ (LlocForeign id).

Definition lloc_own_pub (γ : lloc) (ℓ : loc) : iProp Σ :=
  γ ↪[wrapperGS_γχvirt]□ LlocPublic ℓ.

Instance lloc_own_pub_persistent γ ℓ : Persistent (lloc_own_pub γ ℓ).
Proof using. apply _. Qed.

Instance lloc_own_foreign_persistent γ id : Persistent (lloc_own_foreign γ id).
Proof using. apply _. Qed.

Definition lloc_own_auth (χ : lloc_map) : iProp Σ :=
  "Hχgmap" ∷ ghost_map_auth wrapperGS_γχvirt 1 χ ∗
  "Hχpubs" ∷ ([∗ map] γ↦ℓ ∈ (lloc_map_pubs χ), lloc_own_pub γ ℓ) ∗
  "Hχforeign" ∷ ([∗ map] γ↦id ∈ (lloc_map_foreign χ), lloc_own_foreign γ id).

Notation "γ ~ℓ~ ℓ" := (lloc_own_pub γ ℓ)
  (at level 20, format "γ  ~ℓ~  ℓ").
Notation "γ ~ℓ~/" := (lloc_own_priv γ)
  (at level 20, format "γ  ~ℓ~/").
Notation "γ ~foreign~ id" := (lloc_own_foreign γ id)
  (at level 20, format "γ  ~foreign~  id").

Lemma lloc_own_auth_get_pub_all χ :
  lloc_own_auth χ -∗
  [∗ map] γ↦ℓ ∈ (lloc_map_pubs χ), γ ~ℓ~ ℓ.
Proof using.
  iNamed 1. iApply "Hχpubs".
Qed.

Lemma lloc_own_auth_get_pub χ γ ℓ :
  χ !! γ = Some (LlocPublic ℓ) →
  lloc_own_auth χ -∗
  γ ~ℓ~ ℓ.
Proof using.
  intros Hγ. iNamed 1.
  iDestruct (big_sepM_lookup with "Hχpubs") as "?"; eauto.
Qed.

Lemma lloc_own_auth_get_foreign χ γ id :
  χ !! γ = Some (LlocForeign id) →
  lloc_own_auth χ -∗
  γ ~foreign~ id.
Proof using.
  intros Hγ. iNamed 1.
  iApply (big_sepM_lookup with "Hχforeign"); eauto.
Qed.

Lemma lloc_own_pub_of χ γ ℓ :
  lloc_own_auth χ -∗
  γ ~ℓ~ ℓ -∗
  ⌜χ !! γ = Some (LlocPublic ℓ)⌝.
Proof using.
  iIntros "Hχ Hpub". iNamed "Hχ".
  by iDestruct (ghost_map_lookup with "Hχgmap Hpub") as %?.
Qed.

Lemma lloc_own_priv_of χ γ :
  lloc_own_auth χ -∗
  γ ~ℓ~/ -∗
  ⌜χ !! γ = Some LlocPrivate⌝.
Proof using.
  iIntros "Hχ Hpub". iNamed "Hχ".
  by iDestruct (ghost_map_lookup with "Hχgmap Hpub") as %?.
Qed.

Lemma lloc_own_foreign_of χ γ id :
  lloc_own_auth χ -∗
  γ ~foreign~ id -∗
  ⌜χ !! γ = Some (LlocForeign id)⌝.
Proof using.
  iIntros "Hχ Hfor". iNamed "Hχ".
  by iDestruct (ghost_map_lookup with "Hχgmap Hfor") as %?.
Qed.

Lemma lloc_own_expose χ γ ℓ :
  lloc_own_auth χ -∗
  γ ~ℓ~/ ==∗
  lloc_own_auth (<[γ:=LlocPublic ℓ]> χ) ∗ γ ~ℓ~ ℓ.
Proof using.
  iIntros "Hχ Hγ".
  iDestruct (lloc_own_priv_of with "Hχ Hγ") as %Hχγ.
  iNamed "Hχ".
  iMod (ghost_map_update with "Hχgmap Hγ") as "[$ Hγ]".
  iMod (ghost_map_elem_persist with "Hγ") as "#Hγ".
  iFrame "Hγ". iModIntro. rewrite /named.
  iSplitL "Hχpubs".
  { rewrite lloc_map_pubs_insert_pub.
    iApply big_sepM_insert; eauto.
    apply lloc_map_pubs_lookup_None; eauto. }
  { rewrite lloc_map_foreign_insert_pub delete_notin //.
    destruct (lloc_map_foreign χ !! γ) eqn:Heq; try done.
    apply lloc_map_foreign_lookup_Some in Heq; congruence. }
Qed.

Lemma lloc_own_allocate χ γ:
  ⌜χ !! γ = None⌝ -∗
  lloc_own_auth χ ==∗
  lloc_own_auth (<[γ:=LlocPrivate]> χ) ∗ γ ~ℓ~/.
Proof using.
  iIntros (Hne) "Hχ".
  iNamed "Hχ".
  iMod (ghost_map_insert with "Hχgmap") as "[Hχmap Hγ]"; first done.
  iModIntro. iSplitR "Hγ"; last done.
  iSplitL "Hχmap"; first done. unfold named.
  iSplitL "Hχpubs".
  { rewrite lloc_map_pubs_insert_priv delete_notin.
    2: destruct (lloc_map_pubs χ !! γ) eqn:Heq; try done; apply lloc_map_pubs_lookup_Some in Heq; congruence.
    done. }
  { rewrite lloc_map_foreign_insert_priv delete_notin //.
    destruct (lloc_map_foreign χ !! γ) eqn:Heq; try done.
    apply lloc_map_foreign_lookup_Some in Heq; congruence. }
Qed.

Lemma lloc_own_allocate_foreign χ γ id:
  ⌜χ !! γ = None⌝ -∗
  lloc_own_auth χ ==∗
  lloc_own_auth (<[γ:=LlocForeign id]> χ) ∗ γ ~foreign~ id.
Proof using.
  iIntros (Hne) "Hχ".
  iNamed "Hχ".
  iMod (ghost_map_insert _ (LlocForeign id) with "Hχgmap") as "[Hχmap Hγ]"; first done.
  iMod (ghost_map_elem_persist with "Hγ") as "#Hγ".
  iModIntro. iSplitR "Hγ"; last by iApply "Hγ".
  iSplitL "Hχmap"; first done. unfold named.
  iSplitL "Hχpubs".
  { rewrite lloc_map_pubs_insert_foreign delete_notin.
    2: destruct (lloc_map_pubs χ !! γ) eqn:Heq; try done; apply lloc_map_pubs_lookup_Some in Heq; congruence.
    done. }
  { rewrite lloc_map_foreign_insert_foreign.
    iApply big_sepM_insert; eauto.
    destruct (lloc_map_foreign χ !! γ) eqn:Heq; try done.
    apply lloc_map_foreign_lookup_Some in Heq; congruence. }
Qed.

Lemma lloc_own_insert χ γ v:
  ⌜χ !! γ = None⌝ -∗
  lloc_own_auth χ ==∗
  lloc_own_auth (<[γ:=v]> χ).
Proof using.
  iIntros (Hne) "Hχ".
  destruct v as [l| |].
  { iMod (lloc_own_allocate with "[] Hχ") as "(Hχ & Hγp)"; first done.
    iMod (lloc_own_expose with "Hχ Hγp") as "(H & _)".
    rewrite insert_insert; done. }
  { iMod (lloc_own_allocate_foreign with "[] Hχ") as "(Hχ & Hγ)"; first done.
    by iModIntro. }
  { iMod (lloc_own_allocate with "[] Hχ") as "(Hχ & Hγp)"; first done.
    by iModIntro. }
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
  | F => γ ~ℓ~/
  | M => ∃ ℓ, γ ~ℓ~ ℓ
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
  lstore_own_vblock γ M dq b ⊣⊢ lstore_own_mut γ dq (Bvblock (Mut, b)) ∗ ∃ ℓ, γ ~ℓ~ ℓ.
Proof using.
  iSplit; unfold lstore_own_vblock.
  { iIntros "(? & H)". iDestruct "H" as (?) "?". iFrame. eauto. }
  { iIntros "[[? _] ?]". iFrame. }
Qed.

Lemma lstore_own_vblock_F_as_mut γ dq b :
  lstore_own_vblock γ F dq b ⊣⊢ lstore_own_mut γ dq (Bvblock (Mut, b)) ∗ γ ~ℓ~/.
Proof using.
  iSplit; unfold lstore_own_vblock.
  { iIntros "[? ?]". by iFrame. }
  { iIntros "[[? _] ?]". by iFrame. }
Qed.

Lemma lstore_own_vblock_mutable_as_mut γ dq acc b :
  vblock_access_le M acc →
  lstore_own_vblock γ acc dq b ⊣⊢
  lstore_own_mut γ dq (Bvblock (Mut, b)) ∗
  match acc with F => γ ~ℓ~/ | M => ∃ ℓ, γ ~ℓ~ ℓ | I => True end.
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

Definition lstore_own_foreign γ dq (addr : loc) : iProp Σ :=
  lstore_own_mut γ dq (Bforeign addr) ∗ ∃ id, γ ~foreign~ id.

Notation "γ ↦foreign{ dq } a" := (lstore_own_foreign γ dq a)%I
  (at level 20, format "γ  ↦foreign{ dq }  a") : bi_scope.
Notation "γ ↦foreign a" := (γ ↦foreign{DfracOwn 1} a)%I
  (at level 20, format "γ  ↦foreign  a") : bi_scope.

(* Lifting of ~ℓ~ at the level of ML values *)

Fixpoint block_sim (v : val) (l : lval) : iProp Σ := match v with
  | ML_lang.LitV (ML_lang.LitInt x) => ⌜l = (Lint x)⌝
  | ML_lang.LitV (ML_lang.LitBool b) => ⌜l = (Lint (if b then 1 else 0))⌝
  | ML_lang.LitV ML_lang.LitUnit => ⌜l = (Lint 0)⌝
  | ML_lang.LitV (ML_lang.LitLoc ℓ) => ∃ γ, ⌜l = (Lloc γ)⌝ ∗ γ ~ℓ~ ℓ
  | ML_lang.LitV (ML_lang.LitForeign id) => ∃ γ, ⌜l = (Lloc γ)⌝ ∗ γ ~foreign~ id
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
  1: iExists γ; iSplit; first done.
  1: by iApply (lloc_own_auth_get_pub with "Hχ").
  1: iExists γ, lv1, lv2; iSplit; first done; iSplit.
  3-4: iExists γ, lv; iSplit; first done; iSplit.
  7: iExists γ; iSplit; first done.
  8: iExists γ; iSplit; first done.
  8: by iApply (lloc_own_auth_get_foreign with "Hχ").
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
  all: destruct Hstorebl2 as (ℓ & Vs & Hχ & Hσml); [by eapply elem_of_dom_2|].
  all: efeed specialize Hstore; eauto; [eapply lookup_union_Some; by eauto|].
  all: inversion Hstore.
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

Lemma block_sim_auth_is_val  (ζfreeze ζσ ζvirt : lstore) (χvirt : lloc_map) (σMLvirt : store)
   v b :
  ζfreeze = ζσ ∪ ζvirt →
  is_store_blocks χvirt σMLvirt ζσ →
  is_store χvirt ζfreeze σMLvirt →
  ζσ ##ₘ ζvirt →
  lloc_own_auth χvirt -∗
  lstore_own_auth ζvirt -∗
  b ~~ v -∗
  ⌜is_val χvirt ζfreeze v b⌝.
Proof using.
  iIntros (Hfreeze Hstorebl Hstore Hdis) "Hχ Hζ Hsim".
  iInduction v as [[x|bo| | |]| | | |] "IH" forall (b); cbn.
  all: try (iPure "Hsim" as Hsim; subst; iPureIntro; try econstructor; done).
  1: {iDestruct "Hsim" as "(%γ & -> & Hsim)".
      iPoseProof (lloc_own_pub_of with "Hχ Hsim") as "%HH".
      iPureIntro. econstructor. done. }
  1: { iDestruct "Hsim" as "(%γ & -> & Hsim)".
       iPoseProof (lloc_own_foreign_of with "Hχ Hsim") as "%HH".
       iPureIntro. econstructor. done. }
  1: iDestruct "Hsim" as "(%γ & -> & Hsim)".
  2: iDestruct "Hsim" as "(%γ & %lv1 & %lv2 & -> & Hsim & Hlv1 & Hlv2)";
     iPoseProof ("IH" with "Hχ Hζ Hlv1") as "%Hr1";
     iPoseProof ("IH1" with "Hχ Hζ Hlv2") as "%Hr2".
  3-4: iDestruct "Hsim" as "(%γ & %lv & -> & Hsim & Hlv)";
       iPoseProof ("IH" with "Hχ Hζ Hlv") as "%Hr".
  all: try iDestruct (lstore_own_vblock_I_as_imm with "Hsim") as "Hsim".
  1-4: unshelve iPoseProof (lstore_own_immut_of with "Hζ Hsim") as "[%HH _]".
  all: iPureIntro; econstructor; eauto; by simplify_map_eq.
Qed.

Lemma block_sim_arr_auth_is_val (ζfreeze ζσ ζvirt : lstore) (χvirt : lloc_map) (σMLvirt : store)
   vs bb :
  ζfreeze = ζσ ∪ ζvirt →
  is_store_blocks χvirt σMLvirt ζσ →
  is_store χvirt ζfreeze σMLvirt →
  ζσ ##ₘ ζvirt →
  lloc_own_auth χvirt -∗
  lstore_own_auth ζvirt -∗
  bb ~~∗ vs -∗
  ⌜Forall2 (is_val χvirt ζfreeze) vs bb⌝.
Proof using.
  iIntros (Hfreeze Hstorebl Hstore Hdis) "Hχ Hζ Hsim".
  iPoseProof (big_sepL2_forall with "Hsim") as "(%Heq & Hsim)".
  iAssert (⌜(∀ i x y, vs !! i = Some x → bb !! i = Some y → is_val χvirt ζfreeze x y)⌝)%I as "%HF".
  2: iPureIntro; by apply Forall2_same_length_lookup_2.
  iIntros (i v b H1 H2).
  iApply (block_sim_auth_is_val with "Hχ Hζ"); try done.
  iApply ("Hsim" $! i v b H1 H2).
Qed.

End BasicsResources.

Global Hint Constructors vblock_access_le : core.

(* Re-export notations *)

Notation "γ ~ℓ~ ℓ" := (lloc_own_pub γ ℓ)
  (at level 20, format "γ  ~ℓ~  ℓ").
Notation "γ ~ℓ~/" := (lloc_own_priv γ)
  (at level 20, format "γ  ~ℓ~/").

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

Notation "γ ↦clos ( f , x , e )" := (lstore_own_immut γ (Bclosure f x e))%I
  (at level 20, format "γ  ↦clos  ( f ,  x ,  e )") : bi_scope.

Notation "γ ↦foreign{ dq } a" := (lstore_own_foreign γ dq a)%I
  (at level 20, format "γ  ↦foreign{ dq }  a") : bi_scope.
Notation "γ ↦foreign a" := (γ ↦foreign{DfracOwn 1} a)%I
  (at level 20, format "γ  ↦foreign  a") : bi_scope.

Notation "γ ↦roots{ dq } w" := (γ ↪[wrapperGS_γroots_map]{dq} w)%I
  (at level 20, format "γ  ↦roots{ dq }  w") : bi_scope.
Notation "γ ↦roots w" := (γ ↪[wrapperGS_γroots_map] w)%I
  (at level 20, format "γ  ↦roots  w") : bi_scope.
