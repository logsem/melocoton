From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From iris.base_logic.lib Require Export ghost_map ghost_var.
From iris.algebra.lib Require Import excl_auth gset_bij gmap_view.
From iris.algebra Require Import ofe.
From iris.proofmode Require Import proofmode.
From melocoton Require Import commons.

Section big_sepM_limit.
Context {A B : Type}.
Context `{EqDecision A}.
Context `{Countable A}.
Context `{EqDecision B}.
Context `{Countable B}.
Context {Σ : gFunctors}.

Definition big_sepM_limited (M : gmap A B) (S : gset B) (P : A -> B -> iProp Σ) : iProp Σ := [∗ map] k ↦ v ∈ M, ⌜v ∈ S⌝ -∗ P k v.


Definition split_gmap_by_ran (P : B -> Prop) {D : forall d, Decision (P d)} :
  gmap A B -> gmap A B * gmap A B
  := (map_fold (fun k v '(p1,p2) => if D v then (<[k:=v]>p1,p2) else (p1,<[k:=v]>p2)) (∅, ∅)).

Lemma split_gmap_by_ran_spec P D M M1 M2 :
   (M1,M2) = @split_gmap_by_ran P D M → (forall k v, M1 !! k = Some v -> P v) ∧ (forall k v, M2 !! k = Some v -> ~P v) ∧ (M1 ∪ M2 = M) ∧ (M1 ##ₘ M2).
Proof.
  unfold split_gmap_by_ran. revert M M1 M2.
  apply (@map_fold_ind A (gmap A) _ _ _ _ _ _ _ _ _ _ _
        (fun R M => forall M1 M2, (M1,M2) = R → (forall k v, M1 !! k = Some v -> P v) ∧ (forall k v, M2 !! k = Some v -> ~P v) ∧ (M1 ∪ M2 = M) ∧ (M1 ##ₘ M2))).
  - intros M1 M2. injection 1. intros -> ->. split_and!.
    + intros k v Hc. rewrite lookup_empty in Hc. done.
    + intros k v Hc. rewrite lookup_empty in Hc. done.
    + by rewrite map_union_empty.
    + apply map_disjoint_empty_l.
  - intros k v M [m1 m2] HM IH M1 M2 HM12.
    destruct (IH m1 m2 eq_refl) as (IH1 & IH2 & IH3 & IH4). split_and!.
    + intros k1 v1. destruct (decide (k = k1)) as [-> | Hne]; destruct (D v); injection HM12; intros -> ->.
      * rewrite lookup_insert. injection 1. intros ->. done.
      * apply IH1.
      * rewrite lookup_insert_ne; last done. apply IH1.
      * apply IH1.
    + intros k1 v1. destruct (decide (k = k1)) as [-> | Hne]; destruct (D v); injection HM12; intros -> ->.
      * apply IH2.
      * rewrite lookup_insert. injection 1. intros ->. done.
      * apply IH2.
      * rewrite lookup_insert_ne; last done. apply IH2.
    + destruct (D v); injection HM12; intros -> ->; rewrite <- IH3. 1: by rewrite insert_union_l.
      rewrite insert_union_r; first done. subst M. eapply lookup_union_None_1 in HM. apply HM.
    + destruct (D v);  injection HM12; intros -> ->.
      * apply map_disjoint_insert_l_2; last done. subst M.
        eapply lookup_union_None_1 in HM. apply HM.
      * apply map_disjoint_insert_r_2; last done. subst M.
        eapply lookup_union_None_1 in HM. apply HM.
Qed.

Lemma big_sepM_insert_M M S P x y : 
   ⌜M !! x = None⌝
 -∗ (⌜y ∈ S⌝ -∗ P x y)
 -∗ big_sepM_limited M S P
 -∗ big_sepM_limited (<[ x := y ]> M) S P.
Proof.
  iIntros (Hnone) "HP Hbigsep".
  iApply big_sepM_insert; first done.
  iFrame.
Qed.

Lemma big_sepM_insert_S M S P y : 
    ⌜y ∉ S⌝
 -∗ ([∗ map] k↦v ∈ M, ⌜v = y⌝ -∗ P k v)
 -∗ big_sepM_limited M S P
 -∗ big_sepM_limited M ({[y]} ∪ S) P.
Proof.
  iIntros (Hnone) "HP Hbigsep".
  unfold big_sepM_limited. 
  destruct (split_gmap_by_ran (fun x => x = y) M) as [m1 m2] eqn:Heq.
  symmetry in Heq.
  apply split_gmap_by_ran_spec in Heq.
  destruct Heq as (Heq1 & Heq2 & Heq3 & Hdis). subst M.
  iPoseProof (big_sepM_sep_2 with "HP Hbigsep") as "HH".
  iApply (big_sepM_impl with "HH").
  iIntros "!> %k %v %Hkv (H1 & H2) %Hin".
  apply elem_of_union in Hin. destruct Hin as [Hinl%elem_of_singleton|Hinr].
  + by iApply "H1".
  + by iApply "H2".
Qed.

Lemma big_sepM_insert_inj M S P k y : 
    ⌜gmap_inj M⌝
 -∗ ⌜y ∉ S⌝
 -∗ ⌜M !! k = Some y⌝ 
 -∗ P k y
 -∗ big_sepM_limited M S P
 -∗ big_sepM_limited M ({[y]} ∪ S) P.
Proof.
  iIntros (Hinj Hnone Hsome) "HP Hbigsep".
  unfold big_sepM_limited. 
  destruct (split_gmap_by_ran (fun x => x = y) M) as [m1 m2] eqn:Heq.
  symmetry in Heq.
  apply split_gmap_by_ran_spec in Heq.
  destruct Heq as (Heq1 & Heq2 & Heq3 & Hdis). subst M.
  iPoseProof (big_sepM_union) as "(Hl & _)"; first done.
  iPoseProof ("Hl" with "Hbigsep") as "(Hbigsep1 & Hbigsep2)".
  iClear "Hl".
  iApply big_sepM_union; first done.
  iSplitR "Hbigsep2".
  + assert (m1 = {[k := y]}) as ->.
    1: { apply map_eq_iff. intros k'. destruct (decide (k = k')) as [->|Hn].
    + rewrite lookup_singleton. destruct (m1 !! k') eqn:Heq.
      1: by rewrite (Heq1 k' b Heq).
      enough (y ≠ y) by congruence.
      eapply Heq2. eapply lookup_union_Some_inv_r. 1: apply Hsome. done.
    + rewrite lookup_singleton_ne; last done.
      destruct (m1 !! k') eqn:Heq; try done.
      destruct (m1 !! k) eqn:Heqk.
      2: { eapply lookup_union_Some_inv_r in Heqk; last done.
           enough (y ≠ y) by congruence. eapply Heq2; done. }
      epose proof (Heq1 _ _ Heq) as ->.
      epose proof (Heq1 _ _ Heqk) as ->.
      exfalso. apply Hn. eapply Hinj; eapply lookup_union_Some_l; done. }
    iApply big_sepM_singleton. iIntros "_". done.
  + iApply (big_sepM_impl with "Hbigsep2").
    iIntros "!> %k' %v %Hkv H %Hin".
    iApply "H". iPureIntro. set_solver.
Qed.


Lemma big_sepM_delete_M M S P x y : 
   ⌜M !! x = Some y⌝
 -∗ big_sepM_limited M S P
 -∗ ((⌜y ∈ S⌝ -∗ P x y) ∗ big_sepM_limited (delete x M) S P).
Proof.
  iIntros (Hsome) "HP". iApply (big_sepM_delete _ _ _ _ Hsome with "HP").
Qed.

Lemma big_sepM_delete_S M S P x y : 
   ⌜gmap_inj M⌝
 -∗⌜y ∈ S⌝
 -∗ big_sepM_limited M S P
 -∗ ((⌜M !! x = Some y⌝ -∗ P x y) ∗ big_sepM_limited M (S ∖ {[y]}) P).
Proof.
  iIntros (Hinj Hin) "Hbs".
  destruct (M !! x) eqn:Heq.
  2: iSplitR; first (iIntros "%"; congruence).
  destruct (decide (b = y)) as [-> | ?].
  2: iSplitR; first (iIntros "%"; congruence).
  2-3: iApply (big_sepM_impl with "Hbs"); iIntros "!> %k' %v %Hkv H %Hin2".
  2-3: eapply elem_of_difference in Hin2.
  2-3: iApply "H"; iPureIntro; apply Hin2.
  iPoseProof (big_sepM_delete_M with "[] Hbs") as "(Hl & Hbs)". 1: done.
  iSplitL "Hl".
  1: { iIntros "_". iApply "Hl". done. }
  assert (M = <[ x := y ]> (delete x M)) as HM.
  1: { rewrite map_eq_iff. intros i. destruct (decide (i = x)) as [<- |Hnei].
     + by rewrite lookup_insert.
     + rewrite lookup_insert_ne; last done. by rewrite lookup_delete_ne. }
  rewrite {2} HM.
  iApply (big_sepM_insert). 1: by rewrite lookup_delete.
  iSplitR.
  1: iIntros "%Hf"; exfalso; set_solver.
  iApply (big_sepM_impl with "Hbs []").
  iIntros "!> %k %v %Hk HS %HSk".
  apply elem_of_difference in HSk. iApply "HS". iPureIntro. apply HSk.
Qed.


End big_sepM_limit.



