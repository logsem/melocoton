From Coq Require Import ssreflect.
From stdpp Require Import strings gmap list.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import state lang basics_resources.
From melocoton.interop Require Export basics_constructions.
From transfinite.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Import defs resources.
From melocoton.ml_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.interop Require Import prims weakestpre.
Import Wrap.


Global Notation MLval := ML_lang.val.
Global Notation Cval := C_intf.val.


Section Utils.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.

Implicit Types P : iProp Σ.
Import mlanguage.

Section RootsRepr.

Lemma make_repr θ roots_m roots_fm roots_gm mem :
  roots_m = roots_fm++[roots_gm]
  -> roots_are_live θ roots_m
  -> Forall (map_Forall (λ k v, ∃ w, mem !! k = Some (Storing w) ∧ repr_lval θ v w)) roots_m
  -> ∃ privmem, repr θ roots_m privmem mem.
Proof.
  (* revert roots_m mem roots_hd roots_tl . *)
  (* induction roots_m as [ | roots_hd' roots_tl' HR1 ]. *)
  (* - intros. inversion H. *)
  (* - induction roots_hd' as [|l a roots_hd' Hin IH] using map_ind; *)
  (*   intros mem roots_hd roots_tl  Hroots_m Hlive Hforall. *)
  (* + exists mem, ∅. split_and!. *)
  (*   * econstructor. admit. *)
  (*   * eapply map_disjoint_empty_r. *)
  (*   * by rewrite map_empty_union. *)
  (* + rewrite Forall_cons in Hforall. destruct Hforall as [Hforall Hforalltl ]. *)
  (*   apply map_Forall_insert_1_1 in Hforall as Hforall2. *)
  (*   destruct Hforall2 as (w & Hw & Hrep). *)
  (*   specialize (IH (delete l mem) (delete l roots_hd) roots_tl). *)
  (*   destruct IH as (privmem & memr & IH & Hdisj & Hunion). *)
  (*   1: { admit. } *)
  (*   1: { unfold roots_are_live in *. apply Forall_cons. *)
  (*       apply Forall_cons in Hlive. destruct Hlive as [Hlivehd Hlivetl]. *)
  (*       split; last done. *)
  (*   intros l' g Hg. eapply Hlivehd. rewrite lookup_insert_ne; first done. *)
  (*   intros ->. rewrite Hg in Hin. congruence. } *)
  (*   1: { apply Forall_cons. split. *)
  (*       - apply map_Forall_lookup; intros i x Hinix; *)
  (*         eapply map_Forall_lookup_1 in Hforall. *)
  (*         1: destruct Hforall as (w' & H1 & H2); exists w'; repeat split; try done. *)
  (*         1: rewrite lookup_delete_ne; first done. *)
  (*         2: rewrite lookup_insert_ne; first done. *)
  (*         1-2: intros ->; rewrite Hin in Hinix; congruence. *)
  (*       - admit. } *)
  (*   assert (memr !! l = None) as HNone1. *)
  (*   1: apply not_elem_of_dom; erewrite repr_roots_dom; last done; by eapply not_elem_of_dom. *)
  (*   assert (privmem !! l = None) as Hnone2. *)
  (*   1: rewrite <- (lookup_union_r memr privmem); try done; rewrite <- Hunion; by apply lookup_delete. *)
  (*   eexists privmem, (<[l:=Storing w]> memr). split_and!. *)
  (*   * econstructor; try done; first by eapply not_elem_of_dom. *)
  (*     apply Forall_singleton. by eapply not_elem_of_dom. *)
  (*   * by apply map_disjoint_insert_r. *)
  (*   * erewrite <- insert_union_l. rewrite <- Hunion. rewrite insert_delete_insert. *)
  (*     apply map_eq_iff. intros i. destruct (decide (i = l)) as [-> |]; (try by rewrite lookup_insert); by rewrite lookup_insert_ne. *)
Admitted.

Lemma set_to_none θ mem roots_m privmem :
    repr θ roots_m privmem mem
 -> gen_heap_interp mem
 -∗ ([∗ list] r ∈ roots_m, ([∗ map] a0↦v0 ∈ r, ∃ w, a0 ↦C w ∗ ⌜repr_lval θ v0 w⌝))
==∗ (gen_heap_interp (roots_map_mem' privmem roots_m)
  ∗ [∗ list] r ∈ roots_m, [∗ set] a0 ∈ dom r, a0 O↦C None).
Proof.
(*   intros (mm & Hrepr1 & Hrepr2 & Hrepr3). *)
(*   induction Hrepr1 in Hrepr2,Hrepr3,mem,privmem|-*. *)
(*   + iIntros "Hheap Hmap !>". simpl. *)
(*     rewrite fmap_empty. rewrite dom_empty_L. rewrite map_union_empty. *)
(*     rewrite map_empty_union in Hrepr3. subst mem. iFrame. iSplit; last done. *)
(*     iApply big_sepS_empty. done. *)
(*   + iIntros "Hheap Hmap". *)
(*     iPoseProof (big_sepM_insert) as "(Hb1 & _)"; first apply H0. *)
(*     iPoseProof ("Hb1" with "Hmap") as "((%w' & Hw & %Hrepr4) & Hmap)". *)
(*     repr_lval_inj. *)
(*     iMod (gen_heap_update with "Hheap Hw") as "(Hheap & Hw)". *)
(*     specialize (IHHrepr1 (<[a:=None]> mem) (<[a:=None]> privmem)). *)
(*     iMod (IHHrepr1 with "Hheap Hmap") as "(Hheap & Hmap)". *)
(*     * eapply map_disjoint_insert_l_2; first done. *)
(*       erewrite <- (delete_insert mem0); last done. *)
(*       by eapply map_disjoint_delete_r. *)
(*     * subst mem. erewrite <- insert_union_l. *)
(*       rewrite insert_insert. by rewrite insert_union_r. *)
(*     * iModIntro. iSplitL "Hheap". *)
(*       - erewrite <- insert_union_l. rewrite insert_union_r. *)
(*         2: eapply map_disjoint_Some_r; try done; by rewrite lookup_insert. *)
(*         rewrite fmap_insert. iFrame. *)
(*       - rewrite dom_insert_L. iApply big_sepS_insert; first by eapply not_elem_of_dom. iFrame. *)
(* Qed. *)
Admitted.

Lemma set_to_some θ mem roots_m privmem :
    repr θ roots_m privmem mem
 -> gen_heap_interp (roots_map_mem' privmem roots_m)
 -∗ ([∗ list] r ∈ roots_m, [∗ set] a ∈ dom r, a O↦C None)
 ==∗ gen_heap_interp mem
     ∗ ([∗ list] r ∈ roots_m, [∗ map] a↦v ∈ r, ∃ w, a ↦C w ∗ ⌜repr_lval θ v w⌝).
Proof.
(*   intros (mm & Hrepr1 & Hrepr2 & Hrepr3). *)
(*   induction Hrepr1 in Hrepr2,Hrepr3,mem,privmem|-*. *)
(*   + iIntros "Hheap Hset !>". *)
(*     rewrite fmap_empty. rewrite dom_empty_L. rewrite map_union_empty. *)
(*     rewrite map_empty_union in Hrepr3. subst mem. iFrame. *)
(*     iApply big_sepM_empty. done. *)
(*   + eapply not_elem_of_dom in H0,H1. iIntros "Hheap Hset". *)
(*     rewrite dom_insert_L. *)
(*     iPoseProof (big_sepS_insert) as "(Hb1 & _)"; first eapply not_elem_of_dom_2, H0. *)
(*     iPoseProof ("Hb1" with "Hset") as "(Hw & Hset)". *)
(*     rewrite fmap_insert. rewrite <- insert_union_r. *)
(*     2: eapply map_disjoint_Some_r; first done; by rewrite lookup_insert. *)
(*     iMod (gen_heap_update _ _ _ (Storing w) with "Hheap Hw") as "(Hheap & Hw)". *)
(*     rewrite insert_insert. *)
(*     rewrite insert_union_l. *)
(*     iMod (IHHrepr1 with "Hheap Hset") as "(Hheap & Hset)". *)
(*     * eapply map_disjoint_insert_l_2; first done. *)
(*       erewrite <- (delete_insert mem0); last done. *)
(*       by eapply map_disjoint_delete_r. *)
(*     * done. *)
(*     * rewrite <- insert_union_r; last done. *)
(*       subst mem. rewrite insert_union_l. iModIntro. *)
(*       iFrame. *)
(*       iApply (big_sepM_insert_2 with "[Hw] Hset"). *)
(*       iExists w. iFrame. done. *)
(* Qed. *)
Admitted.

End RootsRepr.

Definition frame_fresh (fs : list gname) (f : gname) :=
  f ∉ fs.

Lemma frame_fresh_infinite (fs : list gname) : pred_infinite (frame_fresh fs).
Proof.
Admitted.

End Utils.
