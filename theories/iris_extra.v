From Coq Require Import ssreflect.
From stdpp Require Import gmap.
From transfinite.base_logic.lib Require Import own gen_heap.
From iris.algebra Require Import auth excl excl_auth gmap.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.

Section Extra.
Context `{SI: indexT}.
Context {Σ : gFunctors}.

Lemma big_sepM_of_pairs {A B} `{Countable A, Countable (A * B)} (m: gmap A B) (Φ : A → B → iProp Σ):
  ([∗ set] p ∈ map_to_set pair m, Φ p.1 p.2) -∗
  ([∗ map] k↦v ∈ m, Φ k v).
Proof.
  induction m using map_ind; first by eauto.
  iIntros "Hs". iApply big_sepM_insert; first done.
  rewrite map_to_set_insert_L//.
  iDestruct (big_sepS_insert with "Hs") as "($&Hs)".
  { intros ?%elem_of_map_to_set_pair. congruence. }
  iApply (IHm with "Hs").
Qed.

Lemma gen_heap_valid_big {L V : Type} {_: EqDecision L} {_: Countable L} {_: gen_heapG L V Σ}
  (σ : gmap L V) (dq : dfrac) (m : gmap L V) :
  gen_heap_interp σ -∗
  ([∗ map] l↦v ∈ m, mapsto l dq v) -∗
  ⌜∃ σ', σ = m ∪ σ' ∧ m ##ₘ σ'⌝.
Proof.
  induction m as [| l v m Hl] using map_ind; iIntros "Hσ Hm".
  { iPureIntro. exists σ. rewrite left_id_L. split; eauto. apply map_disjoint_dom; set_solver. }
  { iDestruct (big_sepM_insert with "Hm") as "(Hl & Hm)"; first done.
    iDestruct (IHm with "Hσ Hm") as %(σ' & -> & Hdisj).
    iDestruct (gen_heap_valid with "Hσ Hl") as %Hσl.
    apply lookup_union_Some_inv_r in Hσl; last done.
    iPureIntro. exists (delete l σ'). split.
    { rewrite union_insert_delete //. }
    { rewrite map_disjoint_dom dom_insert_L dom_delete_L.
      apply map_disjoint_dom in Hdisj. set_solver. } }
Qed.

Lemma gen_heap_update_big {L V : Type} {_: EqDecision L} {_: Countable L} {_: gen_heapG L V Σ}
  (σ σ' σr : gmap L V) :
  dom σ = dom σ' →
  σ ##ₘ σr →
  ([∗ map] l↦v ∈ σ, mapsto l (DfracOwn 1) v) -∗
  gen_heap_interp (σ ∪ σr) ==∗
  ([∗ map] l↦v ∈ σ', mapsto l (DfracOwn 1) v) ∗
  gen_heap_interp (σ' ∪ σr).
Proof.
  revert σ σr. induction σ' as [| l v σ' Hl] using map_ind;
    iIntros (σ σr Hdom Hdisj) "Hpto Hσ".
  { rewrite dom_empty_L in Hdom. apply dom_empty_inv_L in Hdom as ->.
    rewrite left_id_L big_sepM_empty. by iFrame. }
  { rewrite big_sepM_insert//. rewrite dom_insert_L in Hdom.
    assert (is_Some (σ !! l)) as [v' Hv'] by (apply elem_of_dom; set_solver).
    iDestruct (big_sepM_delete with "Hpto") as "[Hl Hpto]"; first done.
    iMod (gen_heap_update _ _ _ v with "Hσ Hl") as "[Hσ $]". 
    apply not_elem_of_dom in Hl.
    iMod (IHσ' (delete l σ) (<[l:=v]> σr) with "Hpto [Hσ]") as "[$ Hσ]".
    { rewrite dom_delete_L Hdom. set_solver. }
    { rewrite map_disjoint_dom dom_delete_L dom_insert_L.
      apply map_disjoint_dom in Hdisj. set_solver. }
    { (* TODO: probably deserves a separate lemma *)
      enough (<[l:=v]> (σ ∪ σr) = delete l σ ∪ <[l:=v]> σr) as ->; first by iFrame.
      apply map_eq. intros i. destruct (decide (i = l)) as [<-|].
      { rewrite lookup_insert lookup_union_r. 2: by rewrite lookup_delete.
        rewrite lookup_insert//. }
      { rewrite lookup_insert_ne//. destruct (decide (is_Some (σ !! i))) as [[? ?]|Hσi].
        { assert (σr !! i = None) by (eapply map_disjoint_Some_l; eauto).
          rewrite !lookup_union_l//. 2: by rewrite lookup_insert_ne//.
          rewrite lookup_delete_ne//. }
        { apply eq_None_not_Some in Hσi. rewrite !lookup_union_r//.
          2: by rewrite lookup_delete_ne. rewrite lookup_insert_ne//. } } }
    rewrite -insert_union_r. 2: by apply not_elem_of_dom. by rewrite insert_union_l. }
Qed.

End Extra.
