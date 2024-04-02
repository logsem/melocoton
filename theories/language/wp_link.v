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

Class can_link (Ψ1 Ψ2 Ψaxiom Ψres : protocol val Σ) (p1 p2 p3 : lang_prog Λ) : Prop := {
  p1_p2_disjoint : dom p1 ## dom p2;
  Ψres_is_union : ⊢ (∀ s vv Φ, Ψres s vv Φ -∗ (Ψ1 ⊔ Ψ2) s vv Φ)%I;
  Ψaxiom_is_axiomatic : ⊢ (∀ s vv Φ, Ψaxiom s vv Φ -∗ ⌜s ∉ dom p3⌝)%I;
  p1_satisfies_Ψ1 : (Ψ2 ⊔ Ψaxiom ||- p1 :: Ψ1);
  p2_satisfies_Ψ2 : (Ψ1 ⊔ Ψaxiom ||- p2 :: Ψ2);
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

Class can_link_all
    (Ψaxiom Ψres : protocol val Σ) (pres : lang_prog Λ)
    (A : list (prod (protocol val Σ) (lang_prog Λ))) := {
  all_disjoint : pairwise (map snd A) (fun p1 p2 => dom p1 ## dom p2);
  Ψres_is_big_union : ⊢ (∀ s vv Φ, Ψres s vv Φ -∗ (spec_union_list (map fst A)) s vv Φ)%I;
  Ψaxiom_is_axiomatic_all : ⊢ (∀ s vv Φ, Ψaxiom s vv Φ -∗ ⌜s ∉ dom pres⌝)%I;
  pres_is_union : pres = union_map_list (map snd A);
  one_spec := fun i => (spec_union_list_except i (map fst A)) ⊔ Ψaxiom;
  all_satisfy_spec : ∀ i, match (nth_error A i) with None => True |
      Some (Ψi, pi) =>  (one_spec i ||- pi :: Ψi)%I end
}.

#[global]
Instance can_link_can_link_all Ψaxiom Ψres pres Ψ1 Ψ2 p1 p2 : can_link Ψ1 Ψ2 Ψaxiom Ψres p1 p2 pres
  -> can_link_all Ψaxiom Ψres pres [(Ψ1,p1); (Ψ2,p2)].
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
    all: iDestruct "H" as "(%HF&H)".
    all: iSplit; first done.
    all: iIntros (Φ') "Hcont".
    all: iApply wp_proto_mono; last iApply "H".
    all: eauto.
    all: cbn; intros s' vv' Φ''; iIntros "[H|H]".
    2,4: by iRight. all: iLeft.
    1: iExists 1. 2: iExists 0.
    all: iSplitR; first done. all: done.
Qed.

Lemma wp_link_execs Ψaxiom Ψres (pres : gmap string (Λ.(func))) A :
  can_link_all Ψaxiom Ψres pres A
  -> ⊢ ∀ e Φ i, match (nth_error A i) with None => ⌜False⌝ | 
          Some (Ψi, pi) => WP e at ⟨pi, (spec_union_list_except i (map fst A)) ⊔ Ψaxiom ⟩ {{ Φ }} end
     -∗ WP e at ⟨pres, Ψaxiom⟩ {{ Φ }}.
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
    iDestruct ("Hsatis" with "HΨ") as "(%HF&HΨ)".
    iSpecialize ("HΨ" $! Ξ with "[]"); first by eauto.
    iDestruct (wp_internal_call_inv with "HΨ") as "H"; first done.
    iDestruct ("H" with "Hσ") as ">[%Hred H]".
    destruct Hred as (?&?&Hstep).
    eapply call_prim_step in Hstep as (F&e'&?&?&?&?); simplify_eq.
    2: { eapply of_call_is_call. }
    iRight. iRight. iModIntro.
    assert (union_map_list (map snd A) !! s' = Some F) as HHF.
    { apply union_map_list_spec. 1: apply Hdis.
      exists pc. split; last done.
      eapply nth_error_In, (in_map snd) in Heqk. apply Heqk. }
    iSplit.
    { iPureIntro. eexists _, _. eapply call_prim_step; eauto. eexists _, _. split_and!; eauto. }
    iIntros (σ' e'1 Hstep).
    eapply call_prim_step in Hstep as (F2&e'2&HF2&He2&->&->); last done; simplify_map_eq.
    assert (e'2 = e') as -> by congruence.
    assert (prim_step pc (of_call Λ s' vv') σ e' σ) as Hstep'.
    { eapply call_prim_step; eauto. 1: eapply of_call_is_call. eexists _, _. split_and!; eauto.
      rewrite fill_empty//. }
    iDestruct ("H" $! _ _ Hstep') as ">H". do 2 iModIntro.
    iDestruct "H" as ">[Hσ H]". iModIntro.
    iFrame "Hσ".
    iApply (wp_bind).
    iApply ("IHe" $! _ _ kidx).
    rewrite Heqk.
    iApply (wp_wand with "H").
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
    iIntros (σ' e' Hstep).
    iSpecialize ("H3" $! σ' e').
    assert (prim_step pi e σ e' σ') as Hstep'.
    { destruct (prim_step_call_dec _ _ _ _ _ Hstep) as [Hcall|Hncall].
      - destruct Hcall as (fn & vs & K & Hcall).
        eapply call_prim_step in Hstep as (f1&?&Hfn&?&->&->); last done.
        destruct HH as (?&?&Hstep'). eapply call_prim_step in Hstep' as (f2&?&Hf2&?&?&->); last done.
        eapply call_prim_step; first done. eexists f1, _; split_and!; eauto. subst.
        apply union_map_list_spec in Hfn as (pj&Hpj&Hfn); last done.
        apply In_nth_error in Hpj as (j&Hpj); apply (map_nth_error snd) in Heq; cbn in Heq.
        destruct (decide (i = j)); first naive_solver.
        specialize (Hdis i j ltac:(assumption)); cbn in Hdis. rewrite Heq Hpj in Hdis.
        apply elem_of_dom_2 in Hfn, Hf2. set_solver.
      - eapply prim_step_no_call; eauto. }
    iDestruct ("H3" $! Hstep') as ">H3". iModIntro. iNext.
    iMod "H3" as "(Hσ & HWP)". iModIntro. iFrame. iApply ("IHe" $! _ _ i). rewrite Heq. done.
Qed.

Lemma wp_link_progs Ψaxiom Ψres (pres : gmap string (Λ.(func))) A :
  can_link_all Ψaxiom Ψres pres A
 -> Ψaxiom ||- pres :: Ψres.
Proof.
  intros [Hdis HΨres Haxiom -> one_spec' Hsatis].
  iIntros (s vv Φ) "H". iPoseProof HΨres as "HΨres".
  iDestruct ("HΨres" with "H") as "[%x Hx]".
  erewrite nth_error_map.
  destruct (nth_error A x) as [[Ψi pi]|] eqn:Heq; last by iExFalso. cbn.
  specialize (Hsatis x) as Hsatis2.
  rewrite Heq in Hsatis2. iDestruct (Hsatis2 with "Hx") as "(%HF&H)".
  iSplit.
  { iPureIntro. apply elem_of_dom in HF as [F HF].
    apply elem_of_dom. eexists.
    apply union_map_list_spec. 1: apply Hdis.
    exists pi. split; last done.
    eapply nth_error_In, (in_map snd) in Heq. apply Heq. }
  { iIntros (Φ') "Hcont".
    iApply (wp_link_execs). 1: done.
    erewrite Heq. iApply "H". eauto. }
Qed.

End wp.
