From iris.proofmode Require Import base proofmode classes.
From transfinite.base_logic.lib Require Export fancy_updates.
From melocoton.language Require Export language weakestpre.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.


Section wp.
Context `{SI:indexT, !langG val Λ Σ, !invG Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr Λ.
Implicit Types T : string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ.
Implicit Types prog : mixin_prog (func Λ).
Implicit Types pe : prog_environ Λ Σ.


Notation mkPe p T := ({| penv_prog := p; penv_proto := T |} : prog_environ Λ Σ).

Definition program_fulfills
  (Tin : program_specification) (p : mixin_prog (func Λ)) (Tshould : program_specification) : iProp Σ := 
  ∀ s vv Φ, Tshould s vv Φ -∗ ⌜p !! s <> None⌝ ∗ WP (of_class _ (ExprCall s vv)) @ (mkPe p Tin); ⊤ {{v, Φ v}}.

Definition env_fulfills
  (p:prog_environ Λ Σ) (Tshould : program_specification) := program_fulfills p.(penv_proto) p.(penv_prog) Tshould.

Notation "Tin '|-' p '::' Tshould" := (program_fulfills Tin p Tshould) (at level 25, p, Tshould at level 26) : bi_scope.

Definition spec_union (p1 p2 : program_specification) : program_specification := 
  λ s vv Φ, (p1 s vv Φ ∨ p2 s vv Φ)%I.
Definition spec_inters (p1 p2 : program_specification) : program_specification := 
  λ s vv Φ, (p1 s vv Φ ∧ p2 s vv Φ)%I.

Notation prog := (gmap string (Λ.(func))).


Class can_link (T1 T2 Taxiom Tres : program_specification) (p1 p2 p3 : prog) : Prop := {
  p1_p2_disjoint : dom p1 ## dom p2;
  Tres_is_union : ⊢ (∀ s vv Φ, Tres s vv Φ -∗ (spec_union T1 T2) s vv Φ)%I;
  Taxiom_is_axiomatic : ⊢ (∀ s vv Φ, Taxiom s vv Φ -∗ ⌜s ∉ dom p3⌝)%I;
  p1_satisfies_T1 : ⊢ (spec_union T2 Taxiom |- p1 :: T1)%I;
  p2_satisfies_T2 : ⊢ (spec_union T1 Taxiom |- p2 :: T2)%I;
  p3_is_union : p3 = (union_with (λ _ _ : func Λ, None) p1 p2);
}.

Definition pairwise {X} (A:list X) (T : X -> X -> Prop) :=
  forall i j, i <> j -> match (nth_error A i, nth_error A j) with
      (Some a, Some b) => T a b
     | _ => True end.

Definition spec_union_list (P : list program_specification) : program_specification := 
  λ s vv Φ, (∃ i, match nth_error P i with Some pp => pp s vv Φ | _ => ⌜False⌝ end)%I.
Definition spec_union_list_except k (P : list program_specification) : program_specification := 
  λ s vv Φ, (∃ i, ⌜i <> k⌝ ∗ match nth_error P i with Some pp => pp s vv Φ | _ => ⌜False⌝ end)%I.

Fixpoint union_map_list (P : list prog) : prog := match P with
  nil => ∅
 | x::xr => union_with (λ _ _ : func Λ, None) x (union_map_list xr)
end.

Lemma pairwise_subset {X} H (a : list X) x : pairwise (x::a) H -> pairwise a H.
Proof.
  intros HH i j Hne.
  specialize (HH (S i) (S j)). cbn in HH.
  apply HH. congruence.
Qed.

Lemma union_map_list_spec x y (P:list prog) : 
  (pairwise P (fun p1 p2 => dom p1 ## dom p2)) -> 
  ((union_map_list P) !! x = Some y <-> ∃ k, In k P ∧ k !! x = Some y).
Proof.
  intros Hdis.
  revert x y.
  induction P; intros x y; first split; cbn.
  - rewrite lookup_empty. intros H; congruence.
  - intros (? & [] & ?).
  - rewrite lookup_union_with.
    destruct (a !! x) as [va|] eqn:Hva;
    destruct (union_map_list P !! x) as [vP|] eqn:HvP; cbn; split; try congruence.
    + intros _. apply IHP in HvP; last by eapply pairwise_subset.
      destruct HvP as (k & (pos & Hpos)%In_nth_error & Heq).
      specialize (Hdis 0 (S pos)); cbn in Hdis. rewrite Hpos in Hdis.
      exfalso. assert (0 ≠ S pos) as Hne by lia. specialize (Hdis Hne).
      rewrite  elem_of_disjoint in Hdis. eapply Hdis.
      all: by eapply elem_of_dom_2.
    + injection 1; intros ->. exists a; repeat split; by try left.
    + intros (k & [-> | Hk] & Heq); first congruence.
      exfalso. assert (∃ k : prog, In k P ∧ k !! x = Some y) as H by by exists k.
      apply IHP in H; first congruence. by eapply pairwise_subset.
    + apply IHP in HvP; last by eapply pairwise_subset.
      destruct HvP as (k & ? & ?).
      injection 1; intros ->. exists k; repeat split; eauto.
    + intros (k & [-> | Hk] & Heq); first congruence.
      assert (∃ k : prog, In k P ∧ k !! x = Some y) as H by by exists k.
      apply IHP in H; last by eapply pairwise_subset. congruence.
    + intros (k & [-> | Hk] & Heq); first congruence.
      assert (∃ k : prog, In k P ∧ k !! x = Some y) as H by by exists k.
      apply IHP in H; last by eapply pairwise_subset. congruence.
Qed.

Lemma union_map_subset A p : 
  (pairwise A (fun p1 p2 => dom p1 ## dom p2)) -> p ∈ A → p ⊆ union_map_list A.
Proof.
  intros Hdis H. apply map_subseteq_spec.
  intros i x Hin.
  apply union_map_list_spec; first done.
  exists p. split; eauto. by apply elem_of_list_In.
Qed.

Class can_link_all 
    (Taxiom Tres : program_specification) (pres : prog)
    (A : list (prod program_specification prog)) := {
  all_disjoint : pairwise (map snd A) (fun p1 p2 => dom p1 ## dom p2);
  Tres_is_big_union : ⊢ (∀ s vv Φ, Tres s vv Φ -∗ (spec_union_list (map fst A)) s vv Φ)%I;
  Taxiom_is_axiomatic_all : ⊢ (∀ s vv Φ, Taxiom s vv Φ -∗ ⌜s ∉ dom pres⌝)%I;
  pres_is_union : pres = union_map_list (map snd A);
  one_spec := fun i => spec_union (spec_union_list_except i (map fst A)) Taxiom;
  all_satisfy_spec : ∀ i, match (nth_error A i) with None => True |
      Some (Ti, pi) =>  ⊢ (one_spec i |- pi :: Ti)%I end
}.

#[global]
Instance can_link_can_link_all Taxiom Tres pres T1 T2 p1 p2 : can_link T1 T2 Taxiom Tres p1 p2 pres
  -> can_link_all Taxiom Tres pres [(T1,p1); (T2,p2)].
Proof.
  intros [H1 H2 H3 H4 H5 H6]; split; cbn.
  - intros [|[|[|i]]] [|[|[|j]]] H; cbn; easy.
  - iIntros (s vv Φ) "Hres". iPoseProof H2 as "H2".
    iDestruct ("H2" $! s vv Φ with "Hres") as "[H2'|H2']".
    + iExists 0; cbn; done.
    + iExists 1; cbn; done.
  - done.
  - rewrite H6. apply map_eq. intros i. rewrite ! lookup_union_with. rewrite lookup_empty.
    destruct (p1 !! i), (p2 !! i); done.
  - intros [|[|[|i]]]; cbn; try done.
    all: iIntros (s vv Φ) "Hres"; cbn.
    1: iPoseProof H4 as "H"; iSpecialize ("H" $! s vv Φ with "Hres").
    2: iPoseProof H5 as "H"; iSpecialize ("H" $! s vv Φ with "Hres").
    all: iDestruct "H" as "[$ HWP]".
    all: iApply wp_pe_mono; last iApply "HWP".
    all: split; first done; cbn; intros s' vv' Φ'; iIntros (Hnot) "[H|H]".
    2,4: by iRight. all: iLeft.
    1: iExists 1. 2: iExists 0.
    all: iSplitR; first done. all: done.
Qed.

Lemma wp_link_execs Taxiom Tres (pres : gmap string (Λ.(func))) A :
  can_link_all Taxiom Tres pres A
  -> ⊢ ∀ e Φ i, match (nth_error A i) with None => ⌜False⌝ | 
          Some (Ti, pi) => WP e @ mkPe pi
          (spec_union (spec_union_list_except i (map fst A)) Taxiom); ⊤ {{ v, Φ v }} end
     -∗ WP e @ mkPe pres (Taxiom); ⊤ {{ v, Φ v }}.
Proof.
  intros [Hdis HTres Haxiom -> one_spec' Hsatis].
  iLöb as "IHe". iIntros (e Φ i).
  destruct (nth_error A i) as [[Ti pi]|] eqn:Heq; last (iIntros "%H"; done).
  rewrite !wp_unfold /wp_pre /=.
  iIntros "H %σ Hσ".
  - iSpecialize ("H" $! σ with "Hσ").
    iMod "H".
    iDestruct "H" as "[(%x & -> & Hσ & H)|[(%s' & %vv' & %K & %HeqK & %H2 & >(%Ξ & Hσ & [HT|HT] & H3))|(%HH & H3)]]".
    * iModIntro. iLeft. iExists _. iFrame. iPureIntro. done.
    * iDestruct "HT" as "(%kidx & %Hknei & HT)". rewrite nth_error_map.
      destruct (nth_error A kidx) as [[Tc pc]|] eqn:Heqk; cbn; last iPure "HT" as [].
      specialize (Hsatis kidx). rewrite Heqk in Hsatis.
      iPoseProof (Hsatis) as "Hsatis".
      iDestruct ("Hsatis" $! s' vv' Ξ with "HT")as "(%HNone & HT)".
      rewrite wp_unfold /wp_pre /=.
      iSpecialize ("HT" $! σ with "Hσ").
      iMod "HT" as "[(%x & %Heqx & Hσ & H)|[(%s'2 & %vv'2 & %K'2 & %HeqK2 & %H''2 & >(%Ξ' & Hσ & HT' & H3'))|(%HH2&H3')]]".
      -- exfalso. apply of_class_inj in Heqx. congruence.
      -- exfalso. assert (K'2 = empty_ectx) as ->. 
         2: { rewrite fill_empty in HeqK2. apply of_class_inj in HeqK2. assert (s'2 = s') as -> by congruence; congruence. }
         destruct (fill_class K'2 (of_class Λ (ExprCall s'2 vv'2))) as [H1|[x Hx]].
         { eexists. rewrite <- HeqK2. by rewrite to_of_class. }
        { done. }
          { exfalso. unfold to_val in Hx. rewrite to_of_class in Hx; congruence. }
     -- destruct HH2 as (e' & σ' & (KK & e1' & e2' & Heq2 & -> & Hstep)%prim_step_inv).
          destruct (fill_class KK e1') as [->|[x Hx]].
         { eexists. rewrite <- Heq2. by rewrite to_of_class. }
         2: { apply val_head_stuck in Hstep. congruence. }
         rewrite ! fill_empty in Heq2. subst e1'.
         apply call_head_step in Hstep.
         destruct Hstep as (Fn & Heqp2' & He2' & -> ). iRight. iRight.
         assert (union_map_list (map snd A) !! s' = Some Fn) as Heqs'.
         { apply union_map_list_spec; first done. exists pc; repeat split; try done.
           apply in_map_iff. exists ((Tc,pc)); repeat split. by eapply nth_error_In. }
         iModIntro. iSplit; first iPureIntro.
         { do 2 eexists. rewrite HeqK. econstructor; first done. 1:done.
           apply call_head_step. exists Fn. repeat split; try done. }
         subst e. iIntros (? ? (e'2 & -> & (Fn3 & Heqp3' & He3' & ->)%call_head_step)%head_reducible_prim_step_ctx).
         2: { do 2 eexists.
              apply call_head_step. exists Fn. repeat split; try done. }
         rewrite Heqs' in Heqp3'. assert (e'2 = e2') as -> by congruence.
         iSpecialize ("H3'" $! σ e2').
         assert (prim_step pc (of_class Λ (ExprCall s' vv')) σ e2' σ) as Hstep2.
         { apply head_prim_step. apply call_head_step. eexists; repeat split; done. }
         iSpecialize ("H3'" $! Hstep2). iMod "H3'". iModIntro. iNext.
         iMod "H3'" as "(? & H3')". iModIntro. iFrame.
         iApply wp_bind. iApply (wp_wand with "[H3']").
         { iApply ("IHe" $! _ _ kidx). rewrite Heqk. iApply "H3'". }
         iIntros (r) "Hr". iSpecialize ("H3" $! r with "Hr"). iApply ("IHe" $! _ _ i). rewrite Heq. done.
    * iRight. iLeft. iModIntro. do 3 iExists _; iSplitR; first done.
      destruct (union_map_list (map snd A) !! s') as [v|] eqn:Heqv.
      { iExFalso. iDestruct (Haxiom $! s' vv' Ξ with "HT") as "%Hfalse". exfalso.
        apply Hfalse. eapply elem_of_dom_2. done. }
      cbn. iSplitR; first done. iModIntro. iExists Ξ. iFrame. iNext.
      iIntros (r) "Hr". iSpecialize ("H3" with "Hr"). iApply ("IHe" $! _ _ i). by rewrite Heq.
    * iModIntro. iRight. iRight.
      iSplitR.
      { iPureIntro. eapply reducible_mono; last done.
        apply union_map_subset; first done. apply elem_of_list_In.
        apply in_map_iff. exists ((Ti, pi)); split; eauto.
        by eapply nth_error_In. }
      iIntros (σ' e' Hstep%prim_step_inv).
      iSpecialize ("H3" $! σ' e').
      destruct Hstep as (K & e1' & e2' & -> & -> & H).
      assert (prim_step pi (fill K e1') σ (fill K e2') σ') as Hstep.
      { econstructor. 1-2:done. destruct (to_class e1') as [[]|] eqn:Heqe1.
        - exfalso. eapply val_head_step. apply of_to_class in Heqe1. erewrite Heqe1. done.
        - apply of_to_class in Heqe1. subst e1'.
          destruct HH as (? & σ'2 & (e2'' & -> & (K2 & eK1 & eK2 & Heq1 & -> & HHstep)%prim_step_inv)%fill_step_inv).
          2: unfold to_val; by rewrite to_of_class.
          assert (K2 = empty_ectx) as ->.
          1: { destruct (fill_class' K2 eK1) as [|[vv Hvv]].
               1: eexists; rewrite <- Heq1; by rewrite to_of_class.
               1: done.
               exfalso. apply of_to_class in Hvv. subst eK1. eapply val_head_step. done. }
          rewrite fill_empty in Heq1. subst eK1. apply call_head_step in H, HHstep.
          destruct H as (FN1 & HFN1 &Happy1 & ->).
          destruct HHstep as (FN2 & HFN2 &Happy2 & ->).
          apply union_map_list_spec in HFN1; last done. destruct HFN1 as (? & [[TT kk] [<- (kki & Hkki)%In_nth_error]]%in_map_iff & HFN1).
          cbn in HFN1. destruct (decide (kki = i)) as [-> | Hcontr].
          1: apply call_head_step; exists FN2; repeat split; try congruence.
          exfalso. specialize (Hdis kki i Hcontr). rewrite ! nth_error_map in Hdis.
          rewrite Hkki in Hdis. rewrite Heq in Hdis. cbn in Hdis. rewrite elem_of_disjoint in Hdis.
          eapply Hdis; eapply elem_of_dom_2; done.
        - by eapply head_step_no_call. }
      iDestruct ("H3" $! Hstep) as ">H3". iModIntro. iNext.
      iMod "H3" as "(Hσ & HWP)". iModIntro. iFrame. iApply ("IHe" $! _ _ i). rewrite Heq. done.
Qed.

Lemma wp_link_progs Taxiom Tres (pres : gmap string (Λ.(func))) A :
  can_link_all Taxiom Tres pres A
 -> ⊢ Taxiom |- pres :: Tres.
Proof.
  intros [Hdis HTres Haxiom -> one_spec' Hsatis].
  iIntros (s vv Φ) "H". iPoseProof HTres as "HTres".
    iDestruct ("HTres" with "H") as "[%x Hx]".
    erewrite nth_error_map.
    destruct (nth_error A x) as [[Ti pi]|] eqn:Heq; last by iExFalso. cbn.
    specialize (Hsatis x) as Hsatis2.
    rewrite Heq in Hsatis2. iDestruct (Hsatis2 $! s vv Φ with "Hx") as "[%Hx1 Hx2]".
    destruct (union_map_list (map snd A) !! s) eqn:Hl2.
  - iSplitR; first done. unshelve iApply (wp_link_execs _ _ _ _ _ $! _ _ x). 3: by split. rewrite Heq. done.
  - exfalso. destruct (pi !! s) as [f|] eqn:Heqpi; try congruence.
    assert (∃ k, In k ((map snd A)) ∧ k !! s = Some f) as HH.
    + exists pi; repeat split; try done. apply in_map_iff. exists (Ti,pi).
      repeat split; try done. eapply nth_error_In. done.
    + apply union_map_list_spec in HH; try congruence. done.
Qed.


End wp.
