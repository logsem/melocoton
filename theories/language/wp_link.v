From iris.proofmode Require Import base proofmode classes.
From transfinite.base_logic.lib Require Export fancy_updates.
From melocoton Require Import stdpp_extra language_commons.
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
Implicit Types Ψ : protocol val Σ.
Implicit Types prog : lang_prog Λ.
Implicit Types pe : prog_environ Λ Σ.

Class can_link E (Ψ1 Ψ2 Ψaxiom Ψres : protocol val Σ) (p1 p2 p3 : lang_prog Λ) : Prop := {
  p1_p2_disjoint : dom p1 ## dom p2;
  Ψres_is_union : ⊢ (∀ s vv Φ, Ψres s vv Φ -∗ (Ψ1 ⊔ Ψ2) s vv Φ)%I;
  Ψaxiom_is_axiomatic : ⊢ (∀ s vv Φ, Ψaxiom s vv Φ -∗ ⌜s ∉ dom p3⌝)%I;
  p1_satisfies_Ψ1 : (Ψ2 ⊔ Ψaxiom ||- p1 @ E :: Ψ1);
  p2_satisfies_Ψ2 : (Ψ1 ⊔ Ψaxiom ||- p2 @ E :: Ψ2);
  p3_is_union : p3 = (union_with (λ _ _ : func Λ, None) p1 p2);
}.

Definition pairwise {X} (A:list X) (Ψ : X -> X -> Prop) :=
  forall i j, i <> j -> match (nth_error A i, nth_error A j) with
      (Some a, Some b) => Ψ a b
     | _ => True end.

Definition spec_union_list (P : list (protocol val Σ)) : protocol val Σ :=
  λ s vv Φ, (∃ i, match nth_error P i with Some pp => pp s vv Φ | _ => ⌜False⌝ end)%I.
Definition spec_union_list_except k (P : list (protocol val Σ)) : protocol val Σ :=
  λ s vv Φ, (∃ i, ⌜i <> k⌝ ∗ match nth_error P i with Some pp => pp s vv Φ | _ => ⌜False⌝ end)%I.

Fixpoint union_map_list (P : list (lang_prog Λ)) : lang_prog Λ := match P with
  nil => ∅
 | x::xr => union_with (λ _ _ : func Λ, None) x (union_map_list xr)
end.

Lemma pairwise_subset {X} H (a : list X) x : pairwise (x::a) H -> pairwise a H.
Proof.
  intros HH i j Hne.
  specialize (HH (S i) (S j)). cbn in HH.
  apply HH. congruence.
Qed.

Lemma union_map_list_spec x y (P:list (lang_prog Λ)) :
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
      exfalso. assert (∃ k : lang_prog Λ, In k P ∧ k !! x = Some y) as H by by exists k.
      apply IHP in H; first congruence. by eapply pairwise_subset.
    + apply IHP in HvP; last by eapply pairwise_subset.
      destruct HvP as (k & ? & ?).
      injection 1; intros ->. exists k; repeat split; eauto.
    + intros (k & [-> | Hk] & Heq); first congruence.
      assert (∃ k : lang_prog Λ, In k P ∧ k !! x = Some y) as H by by exists k.
      apply IHP in H; last by eapply pairwise_subset. congruence.
    + intros (k & [-> | Hk] & Heq); first congruence.
      assert (∃ k : lang_prog Λ, In k P ∧ k !! x = Some y) as H by by exists k.
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

Class can_link_all E
    (Ψaxiom Ψres : protocol val Σ) (pres : lang_prog Λ)
    (A : list (prod (protocol val Σ) (lang_prog Λ))) := {
  all_disjoint : pairwise (map snd A) (fun p1 p2 => dom p1 ## dom p2);
  Ψres_is_big_union : ⊢ (∀ s vv Φ, Ψres s vv Φ -∗ (spec_union_list (map fst A)) s vv Φ)%I;
  Ψaxiom_is_axiomatic_all : ⊢ (∀ s vv Φ, Ψaxiom s vv Φ -∗ ⌜s ∉ dom pres⌝)%I;
  pres_is_union : pres = union_map_list (map snd A);
  one_spec := fun i => (spec_union_list_except i (map fst A)) ⊔ Ψaxiom;
  all_satisfy_spec : ∀ i, match (nth_error A i) with None => True |
      Some (Ψi, pi) =>  (one_spec i ||- pi @ E :: Ψi)%I end
}.

#[global]
Instance can_link_can_link_all E Ψaxiom Ψres pres Ψ1 Ψ2 p1 p2 : can_link E Ψ1 Ψ2 Ψaxiom Ψres p1 p2 pres
  -> can_link_all E Ψaxiom Ψres pres [(Ψ1,p1); (Ψ2,p2)].
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
    1: iPoseProof H4 as "H"; iSpecialize ("H" with "Hres").
    2: iPoseProof H5 as "H"; iSpecialize ("H" with "Hres").
    all: iDestruct "H" as "(%F&%HF&%e&%He&H)".
    all: iExists F; iSplit; first done.
    all: iExists e; iSplit; first done.
    all: iNext.
    all: iApply wp_proto_mono; last iApply "H".
    all: cbn; intros s' vv' Φ'; iIntros "[H|H]".
    2,4: by iRight. all: iLeft.
    1: iExists 1. 2: iExists 0.
    all: iSplitR; first done. all: done.
Qed.

Lemma wp_link_execs E Ψaxiom Ψres (pres : gmap string (Λ.(func))) A :
  can_link_all E Ψaxiom Ψres pres A
  -> ⊢ ∀ e Φ i, match (nth_error A i) with None => ⌜False⌝ | 
          Some (Ψi, pi) => WP e @ ⟨pi, (spec_union_list_except i (map fst A)) ⊔ Ψaxiom ⟩; E {{ Φ }} end
     -∗ WP e @ ⟨pres, Ψaxiom⟩; E {{ Φ }}.
Proof.
  intros [Hdis HΨres Haxiom -> one_spec' Hsatis].
  iLöb as "IHe". iIntros (e Φ i).
  destruct (nth_error A i) as [[Ψi pi]|] eqn:Heq; last (iIntros "%H"; done).
  rewrite !wp_unfold /wp_pre /=.
  iIntros "H %σ Hσ".
  iSpecialize ("H" $! σ with "Hσ").
  iMod "H".
  iDestruct "H" as "[(%x & -> & Hσ & H)|[(%s' & %vv' & %K & %HeqK & %H2 & >(%Ξ & Hσ & [HΨ|HΨ] & H3))|(%HH & H3)]]".
  - iModIntro. iLeft. iExists _. iFrame. iPureIntro. done.
  - iDestruct "HΨ" as "(%kidx & %Hknei & HΨ)". rewrite nth_error_map.
    destruct (nth_error A kidx) as [[Ψc pc]|] eqn:Heqk; cbn; last iPure "HΨ" as [].
    specialize (Hsatis kidx). rewrite Heqk in Hsatis.
    iPoseProof (Hsatis) as "Hsatis".
    iDestruct ("Hsatis" with "HΨ") as "(%F&%HF&%e'&%He'&HΨ)".
    iRight. iRight. iModIntro.
    assert (union_map_list (map snd A) !! s' = Some F) as HHF.
    { apply union_map_list_spec. 1: apply Hdis.
      exists pc. split; last done.
      eapply nth_error_In, (in_map snd) in Heqk. apply Heqk. }
    subst e. assert (head_reducible (union_map_list (map snd A)) ((of_class Λ (ExprCall s' vv'))) σ) as Hredu.
    { do 2 eexists. eapply call_head_step. eexists. split_and!. 2: symmetry; apply He'. all:done. }
    iSplit. 1: iPureIntro; eapply fill_reducible, head_prim_reducible, Hredu.
    iIntros (σ' e'1 (e'2&->&(F2&HF2&He2&->)%call_head_step_inv)%head_reducible_prim_step_ctx); last done.
    simplify_eq. assert (e'2 = e') as -> by congruence.
    do 3 iModIntro. iFrame "Hσ".
    iApply (wp_bind).
    iApply ("IHe" $! _ _ kidx).
    rewrite Heqk.
    iApply (wp_wand with "HΨ").
    iIntros (v) "Hv".
    iApply ("IHe" $! _ _ i).
    rewrite Heq.
    iApply ("H3" with "Hv").
  - iRight. iLeft. iModIntro. do 3 iExists _; iSplitR; first done.
    destruct (union_map_list (map snd A) !! s') as [v|] eqn:Heqv.
    { iExFalso. iDestruct (Haxiom $! s' vv' Ξ with "HΨ") as "%Hfalse". exfalso.
      apply Hfalse. eapply elem_of_dom_2. done. }
    cbn. iSplitR; first done. iModIntro. iExists Ξ. iFrame. iNext.
    iIntros (r) "Hr". iSpecialize ("H3" with "Hr"). iApply ("IHe" $! _ _ i). by rewrite Heq.
  - iModIntro. iRight. iRight.
    iSplitR.
    { iPureIntro. eapply reducible_mono; last done.
      apply union_map_subset; first done. apply elem_of_list_In.
      apply in_map_iff. exists ((Ψi, pi)); split; eauto.
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
        apply union_map_list_spec in HFN1; last done. destruct HFN1 as (? & [[ΨΨ kk] [<- (kki & Hkki)%In_nth_error]]%in_map_iff & HFN1).
        cbn in HFN1. destruct (decide (kki = i)) as [-> | Hcontr].
        1: apply call_head_step; exists FN2; repeat split; try congruence.
        exfalso. specialize (Hdis kki i Hcontr). rewrite ! nth_error_map in Hdis.
        rewrite Hkki in Hdis. rewrite Heq in Hdis. cbn in Hdis. rewrite elem_of_disjoint in Hdis.
        eapply Hdis; eapply elem_of_dom_2; done.
      - by eapply head_step_no_call. }
    iDestruct ("H3" $! Hstep) as ">H3". iModIntro. iNext.
    iMod "H3" as "(Hσ & HWP)". iModIntro. iFrame. iApply ("IHe" $! _ _ i). rewrite Heq. done.
Qed.

Lemma wp_link_progs E Ψaxiom Ψres (pres : gmap string (Λ.(func))) A :
  can_link_all E Ψaxiom Ψres pres A
 -> Ψaxiom ||- pres @ E :: Ψres.
Proof.
  intros [Hdis HΨres Haxiom -> one_spec' Hsatis].
  iIntros (s vv Φ) "H". iPoseProof HΨres as "HΨres".
  iDestruct ("HΨres" with "H") as "[%x Hx]".
  erewrite nth_error_map.
  destruct (nth_error A x) as [[Ψi pi]|] eqn:Heq; last by iExFalso. cbn.
  specialize (Hsatis x) as Hsatis2.
  rewrite Heq in Hsatis2. iDestruct (Hsatis2 with "Hx") as "(%F&%HF&%e&%He&H)".
  iExists F. iSplit.
  - iPureIntro. apply union_map_list_spec. 1: apply Hdis.
    exists pi. split; last done.
    eapply nth_error_In, (in_map snd) in Heq. apply Heq.
  - iExists e. iSplit; first done. iNext.
    iApply (wp_link_execs). 1: done.
    erewrite Heq. iApply "H".
Qed.


End wp.
