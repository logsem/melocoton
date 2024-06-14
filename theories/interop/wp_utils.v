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

(* We can decompose mem, the C heap, into a privmem, which is everything but the
   roots, and a memr, which are just the rooted cells *)
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
    1: rewrite <- (lookup_union_r memr privmem); try done; rewrite <- Hunion; by apply lookup_delete.
    eexists privmem, (<[l:=Storing w]> memr). split_and!.
    * econstructor; try done; by eapply not_elem_of_dom.
    * by apply map_disjoint_insert_r.
    * erewrite <- insert_union_l. rewrite <- Hunion. rewrite insert_delete_insert.
      apply map_eq_iff. intros i. destruct (decide (i = l)) as [-> |]; (try by rewrite lookup_insert); by rewrite lookup_insert_ne.
Qed.

Lemma set_to_none θ mem roots_m privmem :
    repr θ roots_m privmem mem
 -> gen_heap_interp mem
 -∗ ([∗ map] a0↦v0 ∈ roots_m, ∃ w, a0 ↦C{DfracOwn 1} w ∗ ⌜repr_lval θ v0 w⌝)
==∗ (gen_heap_interp (privmem ∪ ((λ _ : lval, None) <$> roots_m))
    ∗[∗ set] a0 ∈ dom roots_m, a0 O↦C None).
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
    repr_lval_inj.
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

Lemma repr_roots_repr_lval θ roots m : repr_roots θ roots m -> forall k v, roots !! k = Some v -> exists w, m !! k = Some (Storing w) /\ repr_lval θ v w.
Proof.
  induction 1; intros ??.
  - intros H. rewrite lookup_empty in H. done.
  - intros [[<- <-]|[Hn1 Hn2]]%lookup_insert_Some.
    + rewrite lookup_insert. econstructor. done.
    + rewrite lookup_insert_ne. 2: done. apply IHrepr_roots. done.
Qed.

Lemma repr_dom_eq θ mem roots_1 roots_2 p1 p2 m1 m2 :
   dom roots_1 = dom roots_2
 → gmap_inj θ
 → repr_raw θ roots_1 p1 mem m1
 → repr_raw θ roots_2 p2 mem m2
 → p1 = p2 ∧ m1 = m2 ∧ roots_1 = roots_2.
Proof.
  intros H1 Hinj (Hr1&Hd1&Hu1) (Hr2&Hd2&Hu2).
  assert (m1 = m2) as ->.
  { apply repr_roots_dom in Hr1,Hr2. rewrite H1 in Hr1. rewrite Hr1 in Hr2.
    eapply map_eq_iff. intros i. destruct (m1 !! i) as [v|] eqn:Heq.
    + eapply elem_of_dom_2 in Heq as Hdom. eapply lookup_union_Some_l in Heq.
      erewrite <- Hu1 in Heq. erewrite <- Heq. erewrite Hu2.
      rewrite Hr2 in Hdom.
      eapply lookup_union_l. apply elem_of_dom in Hdom as [vv Hvv].
      eapply map_disjoint_Some_l. 1: done. apply Hvv.
    + symmetry. eapply not_elem_of_dom. rewrite <- Hr2. by eapply not_elem_of_dom. }
  assert (p1 = p2) as ->.
  { eapply map_eq_iff. intros i. destruct (p1 !! i) as [v|] eqn:Heq.
    + eapply elem_of_dom_2 in Heq as Hdom. eapply lookup_union_Some_r in Heq. 2: done.
      erewrite <- Hu1 in Heq. erewrite <- Heq. erewrite Hu2;
      eapply lookup_union_r.
      eapply not_elem_of_dom. eapply map_disjoint_dom in Hd1. set_solver.
    + destruct (mem !! i) as [v'|] eqn:Heqmem.
      * pose proof Heqmem as Heq2. rewrite Hu1 in Heqmem.
        apply lookup_union_Some_inv_l in Heqmem. 2: done. symmetry.
        eapply map_disjoint_Some_r. 1: done. done.
      * rewrite Hu2 in Heqmem. apply lookup_union_None_1 in Heqmem. symmetry. apply Heqmem. }
  split_and!; try done.
  pose proof (repr_roots_repr_lval _ _ _ Hr2) as Hr2'.
  clear Hd1 Hu1 Hd2 Hu2 Hr2.
  induction Hr1 in Hinj, roots_2, H1, Hr2'|-*.
  { rewrite dom_empty_L in H1. symmetry in H1. apply dom_empty_inv_L in H1. done. }
  destruct (roots_2 !! a) as [v2|] eqn:Heq.
  2: { eapply not_elem_of_dom in Heq. rewrite <- H1 in Heq. erewrite dom_insert_L in Heq. set_solver. }
  erewrite <- (insert_delete roots_2 a v2); last done. f_equiv.
  - destruct (Hr2' a v2 Heq) as (ww & Heqw & Hrepr).
    rewrite lookup_insert in Heqw. injection Heqw; intros ->.
    by eapply repr_lval_inj_1.
  - eapply IHHr1.
    + rewrite dom_delete_L. rewrite <- H1. set_solver.
    + done.
    + intros k1 v1 [H3 H4]%lookup_delete_Some.
      destruct (Hr2' _ _ H4) as (ww&[[??]|[? ?]]%lookup_insert_Some&Hww2).
      1: done.
      by exists ww.
Qed.

Lemma set_to_some θ mem roots_m privmem :
    repr θ roots_m privmem mem
 -> gen_heap_interp (privmem ∪ ((λ _ : lval, None) <$> roots_m))
 -∗ ([∗ set] a ∈ dom roots_m, a O↦C None)
 ==∗ gen_heap_interp mem
     ∗ ([∗ map] a↦v ∈ roots_m, ∃ w, a ↦C{DfracOwn 1} w ∗ ⌜repr_lval θ v w⌝).
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

End RootsRepr.

End Utils.
