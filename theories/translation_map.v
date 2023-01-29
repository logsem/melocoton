From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import commons.

Section TranslationMap.

Context (A B : Type).
Context `{Countable A}.
Context `{Countable B}.
Context `{Infinite A}.
Context `{Infinite B}.

Definition translation_map := gmap A B.

Definition is_translation_map (m : translation_map) (MA : gset A) (MB : gset B) :=
     gmap_inj m
  /\ (forall k, k ∈ MA → k ∈ dom m)
  /\ (forall k, k ∈ MB → (exists x, m !! x = Some k)).

Lemma tm_insert_l m l MA MB : is_translation_map m MA MB ->
  exists m', m ⊆ m' ∧ is_translation_map m' (MA ∪ {[l]}) MB.
Proof.
  intros HH.
  destruct (m !! l) eqn:Heq.
  + exists m. split; first done.
    destruct HH as (HH1 & HH2 & HH3); split; first done.
    split; last done.
    intros k [Hin| -> % elem_of_singleton]%elem_of_union. 1: by apply HH2.
    eapply elem_of_dom. by exists b.
  + pose (fresh (map_to_set (fun a b => b) m : gset B)) as r.
    exists (<[ l := r ]> m). destruct HH as (HH1 & HH2 & HH3). repeat split.
    * by apply insert_subseteq.
    * intros k1 k2 v. intros [[? ?]|[Hne1 Hk1]]%lookup_insert_Some [[? ?]|[Hne2 Hk2]]%lookup_insert_Some; subst.
      - done.
      - exfalso. eapply (is_fresh (map_to_set (fun a b => b) m : gset B)).
        eapply elem_of_map_to_set. do 2 eexists; repeat split; try done.
      - exfalso. eapply (is_fresh (map_to_set (fun a b => b) m : gset B)).
        eapply elem_of_map_to_set. do 2 eexists; repeat split; try done.
      - eapply HH1; done.
    * intros k [Hin| -> % elem_of_singleton]%elem_of_union; rewrite dom_insert_L.
      - eapply elem_of_union_r. eapply HH2. done.
      - eapply elem_of_union_l, elem_of_singleton. done.
    * intros k Hk. destruct (HH3 k Hk) as (x & Hx). exists x. rewrite lookup_insert_ne; first done.
      intros <-. rewrite Heq in Hx. done.
Qed.

Lemma tm_insert_r m r MA MB : is_translation_map m MA MB ->
  exists m', m ⊆ m' ∧ is_translation_map m' (MA) (MB ∪ {[r]}).
Proof.
  intros HH.
  pose ((map_to_set (fun a b => b) m : gset B)) as mdom.
  destruct (decide (r ∈ mdom)) as [Hin|Hnot].
  + exists m. split; first done.
    destruct HH as (HH1 & HH2 & HH3); split; first done.
    split; first done.
    intros k [Hink| -> % elem_of_singleton]%elem_of_union. 1: by apply HH3.
    eapply elem_of_map_to_set in Hin. destruct Hin as (i & x & HS & ->).
    exists i; done.
  + pose (fresh (dom m)) as l.
    exists (<[ l := r ]> m). destruct HH as (HH1 & HH2 & HH3). repeat split.
    * apply insert_subseteq. eapply not_elem_of_dom. eapply is_fresh.
    * intros k1 k2 v. intros [[? ?]|[Hne1 Hk1]]%lookup_insert_Some [[? ?]|[Hne2 Hk2]]%lookup_insert_Some; subst.
      - done.
      - exfalso. apply Hnot.
        eapply elem_of_map_to_set. do 2 eexists; repeat split; try done.
      - exfalso. apply Hnot.
        eapply elem_of_map_to_set. do 2 eexists; repeat split; try done.
      - eapply HH1; done.
    * intros k Hk. rewrite dom_insert_L. eapply elem_of_union_r. by apply HH2.
    * intros k [Hin| -> % elem_of_singleton]%elem_of_union.
      - destruct (HH3 k Hin) as (v & Hv). exists v. rewrite lookup_insert_ne; first done. intros <-.
        eapply (is_fresh (dom m)). eapply elem_of_dom. exists k. apply Hv.
      - exists l. rewrite lookup_insert. done.
Qed.

Lemma tm_bulk_update (m:translation_map) (MA MA' : gset A) (MB MB' : gset B) :
    is_translation_map m MA MB
 -> MA ⊆ MA'
 -> MB ⊆ MB'
 -> exists (m':translation_map), m ⊆ m' /\ is_translation_map m' MA' MB'.
Proof.
  intros Hmap H3 H4.
Abort.








End TranslationMap.