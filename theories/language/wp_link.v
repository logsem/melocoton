From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From melocoton.language Require Export language weakestpre.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.


Section wp.
Context `{!melocotonGS_gen hlc val Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types e : expr Λ.
Implicit Types T : string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ.
Implicit Types prog : mixin_prog (func Λ).
Implicit Types pe : prog_environ.

Lemma wp_link pe pe_extended F k E e Φ :
  ⌜ k ∉ dom (prog pe) ⌝
  -∗ ⌜ prog pe_extended = <[ k := F ]> (prog pe) ⌝ 
  -∗ (□ (∀ (s:string) vv Ψ, ⌜s ∉ (dom (prog pe)) ∧ s <> k⌝ -∗ T pe s vv Ψ -∗ T (pe_extended) s vv Ψ))
  -∗ (□ (∀ vv Ψ, T pe k vv Ψ -∗ WP (of_class Λ (ExprCall k vv)) @ (pe_extended); E {{v, Ψ v}}))
  -∗ WP e @ pe; E {{v, Φ v}}
  -∗ WP e @ (pe_extended); E {{v, Φ v}}.
Proof.
  iIntros (HnE HE) "#Hs2T #Hs1T H". iLöb as "IH" forall (e Φ).
  rewrite !wp_unfold /wp_pre /=.
  iIntros "%σ %ns Hσ". iSpecialize ("H" $! σ ns with "Hσ").
  iMod "H".
  iDestruct "H" as "[(%x & -> & Hσ & H)|[(%s & %vv & %K & -> & %H2 & H3)|(%HH & H3)]]".
  - iLeft. iExists x. iFrame. iModIntro. done.
  - iMod "H3" as "(%Ξ & Hσ & HT & Hcont)". destruct (decide (k = s)) as [->|Hne]. 
    + iPoseProof ("Hs1T" with "HT") as "HT'".
      rewrite !(wp_unfold pe_extended E (of_class Λ (ExprCall s vv))) /wp_pre /=.
      iMod ("HT'" $! σ ns with "Hσ") as "HT'".
      iDestruct "HT'" as "[ (%x & %Hcontr & Hσ & H) |[ (%s' & %vv' & %K' & %Hcontr & %H2' & H3') |(%HH' & H3)]]".
      { exfalso.
        enough (to_class (of_class Λ (ExprCall s vv)) = to_class (of_class Λ (ExprVal x))) by
          (repeat rewrite to_of_class in H; congruence).
        congruence. }
      { exfalso.
        destruct (fill_class K' (of_class Λ (ExprCall s' vv'))) as [->|HR].
        - rewrite <- Hcontr. rewrite to_of_class. by eexists.
        - rewrite fill_empty in Hcontr. 
          assert (to_class (of_class Λ (ExprCall s vv)) = to_class (of_class Λ (ExprCall s' vv'))) as H by congruence.
          do 2 rewrite to_of_class in H. assert (s' = s) as -> by congruence.
          rewrite HE in H2'. rewrite lookup_insert in H2'. congruence.
        - unfold to_val in HR. rewrite to_of_class in HR. by destruct HR. }
      iModIntro.
      iRight. iRight.
      iSplitR.
      { iPureIntro. eapply reducible_no_threads_fill. done. }
      iIntros "%σ' %e' %Hstep".
      apply fill_reducible_prim_step in Hstep.
      2: { by eapply reducible_no_threads_reducible. }
      destruct Hstep as (e'' & -> & Hstep).
      iSpecialize ("H3" $! σ' _ Hstep). iMod "H3". do 1 iModIntro. iNext. iMod "H3" as "(H31 & H32)".
      iModIntro. iFrame. iApply wp_bind. iApply (wp_wand with "[H32]").
      * iApply "H32".
      * iIntros (v) "Hv". iSpecialize ("Hcont" $! v with "Hv"). iApply "IH". done.
    + iPoseProof ("Hs2T" with "[] HT") as "HT'"; first iPureIntro.
      { split; try congruence. by apply not_elem_of_dom_2. }
      iModIntro. iRight. iLeft. iExists s, vv, K.
      iSplitR; first done. iSplitR.
      { iPureIntro. rewrite HE. by rewrite lookup_insert_ne. }
      iModIntro. iExists Ξ. iFrame. iNext. iIntros (r) "Hr". iApply "IH".
      iApply ("Hcont" with "Hr").
  - iModIntro. iRight. iRight.
    destruct HH as (? & σ' & (K & e1' & e2' & -> & -> & HH)%prim_step_inv).
    destruct (to_class e1') as [[v|s vv]|] eqn:Heq.
    + apply of_to_class in Heq. rewrite <- Heq in HH. exfalso. eapply val_head_step. done.
    + apply of_to_class in Heq. subst e1'. apply call_head_step_inv in HH.
      destruct HH as (fn & Hs & Hfn & -> & _). assert (k ≠ s) as Hne.
      { intros ->. apply elem_of_dom_2 in Hs. done. }
      iSplitR.
      { iPureIntro. eexists _,_. econstructor. 1-2:done. apply call_head_step.
        exists fn; repeat split; try done. rewrite HE. by rewrite lookup_insert_ne. }
      iIntros (σ' e' Hstep).
      assert (prim_step (prog pe) (fill K (of_class Λ (ExprCall s vv))) σ (fill K e2') σ []) as Hstep'.
      { econstructor. 1-2:done. eapply call_head_step. exists fn; repeat split; done. }
      apply head_reducible_prim_step_ctx in Hstep; last first.
      1: eexists _, _, _; apply call_head_step; eexists; repeat split; try done;
         rewrite HE; by rewrite lookup_insert_ne.
      destruct Hstep as (e3 & Heq3 & (ffn & Heq4 & Heq5 & -> & _)%call_head_step_inv).
      iSpecialize ("H3" $! _ _ Hstep').
      iMod "H3". iModIntro. iNext. iMod "H3" as "(Hσ' & HWP)". iModIntro.
      iFrame. iApply "IH". enough (e' = fill K e2') as -> by done.
      rewrite HE in Heq4. rewrite lookup_insert_ne in Heq4; last done.
      rewrite Hs in Heq4. congruence.
    + iSplitR.
      { iPureIntro. eexists _,_. eapply head_step_no_call in HH. 
        1: econstructor; first done; first done.
        1: apply HH. 1: done. (*
        rewrite HE. apply insert_subseteq. by apply not_elem_of_dom_1. *) }
      iIntros (σ'' e'' Hstep).
      apply head_reducible_prim_step_ctx in Hstep; last first.
      { eexists _,_,_. eapply head_step_no_call in HH. 
        1: apply HH. 1: done. (*
        rewrite HE. apply insert_subseteq. by apply not_elem_of_dom_1. *) }
      destruct Hstep as (e2'' & -> & Hstep).
      eapply head_step_no_call in Hstep; last done.
      iMod ("H3" $! _ _ (Prim_step _ _ _ _ _ _ _ _ _ eq_refl eq_refl Hstep)) as "H3".
      iModIntro. iNext. iMod "H3" as "(Hσ'' & Hfill)". iModIntro. iFrame.
      iApply "IH". iFrame.
Qed.


Lemma wp_link_rec pe pe_extended F k E e Φ :
  ⌜ k ∉ dom (prog pe) ⌝
  -∗ ⌜ prog pe_extended = <[ k := F ]> (prog pe) ⌝ 
  -∗ (□ (∀ (s:string) vv Ψ, ⌜s ∉ (dom (prog pe)) ∧ s <> k⌝ -∗ T pe s vv Ψ -∗ T (pe_extended) s vv Ψ))
  -∗ (□ (∀ vv Ψ, T pe k vv Ψ -∗ WPFun F with vv @ (pe); E {{v, Ψ v}}))
  -∗ WP e @ pe; E {{v, Φ v}}
  -∗ WP e @ (pe_extended); E {{v, Φ v}}.
Proof.
  iIntros (HnE HE) "#Hs2T #Hs1T H". iLöb as "IH" forall (e Φ).
  rewrite !wp_unfold /wp_pre /=.
  iIntros "%σ %ns Hσ". iSpecialize ("H" $! σ ns with "Hσ").
  iMod "H".
  iDestruct "H" as "[(%x & -> & Hσ & H)|[(%s & %vv & %K & -> & %H2 & H3)|(%HH & H3)]]".
  - iLeft. iExists x. iFrame. iModIntro. done.
  - iMod "H3" as "(%Ξ & Hσ & HT & Hcont)". destruct (decide (k = s)) as [->|Hne]. 
    + iPoseProof ("Hs1T" with "HT") as "HT'". unfold wp_func at 2.
      destruct (apply_func F vv) as [e'|] eqn:Heq; try done.
      iRight. iRight. iMod "HT'". iModIntro.
      assert (head_step (prog pe_extended) (of_class Λ (ExprCall s vv)) σ e' σ []) as Hstepy.
      1: apply call_head_step; exists F; split; first (rewrite HE; by rewrite lookup_insert); by repeat split.
      iSplitR.
      1: iPureIntro; eexists _,_; by econstructor.
      iIntros (σ' e'' (e2'' & -> & (F' & HeqF' & HeqF'a & -> & HH)%call_head_step_inv)%head_reducible_prim_step_ctx).
      2: do 3 eexists; done.
      iModIntro. iNext. iMod "HT'". iMod (state_interp_mono with "Hσ" ) as "Hσ". iModIntro. iFrame.
      iApply "IH". rewrite HE in HeqF'. rewrite (lookup_insert) in HeqF'. iApply wp_bind.
      assert (e' = e2'') as -> by congruence.
      iApply (wp_wand with "HT'").
      iIntros (v) "Hv". iApply ("Hcont" $! v with "Hv").
    + iPoseProof ("Hs2T" with "[] HT") as "HT'"; first iPureIntro.
      { split; try congruence. by apply not_elem_of_dom_2. }
      iModIntro. iRight. iLeft. iExists s, vv, K.
      iSplitR; first done. iSplitR.
      { iPureIntro. rewrite HE. by rewrite lookup_insert_ne. }
      iModIntro. iExists Ξ. iFrame. iNext. iIntros (r) "Hr". iApply "IH".
      iApply ("Hcont" with "Hr").
  - iModIntro. iRight. iRight.
    destruct HH as (? & σ' & (K & e1' & e2' & -> & -> & HH)%prim_step_inv).
    destruct (to_class e1') as [[v|s vv]|] eqn:Heq.
    + apply of_to_class in Heq. rewrite <- Heq in HH. exfalso. eapply val_head_step. done.
    + apply of_to_class in Heq. subst e1'. apply call_head_step_inv in HH.
      destruct HH as (fn & Hs & Hfn & -> & _). assert (k ≠ s) as Hne.
      { intros ->. apply elem_of_dom_2 in Hs. done. }
      iSplitR.
      { iPureIntro. eexists _,_. econstructor. 1-2:done. apply call_head_step.
        exists fn; repeat split; try done. rewrite HE. by rewrite lookup_insert_ne. }
      iIntros (σ' e' Hstep).
      assert (prim_step (prog pe) (fill K (of_class Λ (ExprCall s vv))) σ (fill K e2') σ []) as Hstep'.
      { econstructor. 1-2:done. eapply call_head_step. exists fn; repeat split; done. }
      apply head_reducible_prim_step_ctx in Hstep; last first.
      1: eexists _, _, _; apply call_head_step; eexists; repeat split; try done;
         rewrite HE; by rewrite lookup_insert_ne.
      destruct Hstep as (e3 & Heq3 & (ffn & Heq4 & Heq5 & -> & _)%call_head_step_inv).
      iSpecialize ("H3" $! _ _ Hstep').
      iMod "H3". iModIntro. iNext. iMod "H3" as "(Hσ' & HWP)". iModIntro.
      iFrame. iApply "IH". enough (e' = fill K e2') as -> by done.
      rewrite HE in Heq4. rewrite lookup_insert_ne in Heq4; last done.
      rewrite Hs in Heq4. congruence.
    + iSplitR.
      { iPureIntro. eexists _,_. eapply head_step_no_call in HH. 
        1: econstructor; first done; first done.
        1: apply HH. 1: done. (*
        rewrite HE. apply insert_subseteq. by apply not_elem_of_dom_1. *) }
      iIntros (σ'' e'' Hstep).
      apply head_reducible_prim_step_ctx in Hstep; last first.
      { eexists _,_,_. eapply head_step_no_call in HH. 
        1: apply HH. 1: done. (*
        rewrite HE. apply insert_subseteq. by apply not_elem_of_dom_1. *) }
      destruct Hstep as (e2'' & -> & Hstep).
      eapply head_step_no_call in Hstep; last done.
      iMod ("H3" $! _ _ (Prim_step _ _ _ _ _ _ _ _ _ eq_refl eq_refl Hstep)) as "H3".
      iModIntro. iNext. iMod "H3" as "(Hσ'' & Hfill)". iModIntro. iFrame.
      iApply "IH". iFrame.
Qed.

Notation mkPe p T := (Build_prog_environ _ _ _ _ _ p T).

Definition program_fulfills
  (Tin : program_specification) (p : mixin_prog (func Λ)) (Tshould : program_specification) : iProp Σ := 
  ∀ s vv Φ, Tshould s vv Φ -∗ ⌜p !! s <> None⌝ ∗ WP (of_class _ (ExprCall s vv)) @ (mkPe p Tin); ⊤ {{v, Φ v}}.

Notation "Tin '|-' p '::' Tshould" := (program_fulfills Tin p Tshould) (at level 25, p, Tshould at level 26) : bi_scope.

Definition spec_union (p1 p2 : program_specification) : program_specification := 
  λ s vv Φ, (p1 s vv Φ ∨ p2 s vv Φ)%I.
Definition spec_inters (p1 p2 : program_specification) : program_specification := 
  λ s vv Φ, (p1 s vv Φ ∧ p2 s vv Φ)%I.

(*
Lemma link_progs T1 T2 (p1 : gmap string (Λ.(func))) F s':
    ⌜s' ∉ dom p1⌝
 -∗ □(T2 |- p1 :: T1)
 -∗ □(∀ vv Φ, T2 s' vv Φ -∗ WP (of_class _ (ExprCall s' vv)) @ (mkPe ∅ T1); ⊤ {{v, Φ v}})
 -∗ (λ s vv Φ, T2 s vv Φ ∧ ⌜s <> s'⌝) |- (<[s':=F]> p1) :: (spec_union T1 (λ s vv Φ, ⌜s = s'⌝ ∧ T2 s vv Φ)).
Proof.
  iIntros (Hdom) "#Hp1 #Hp2".
  iAssert (∀ Φ e, ((WP e @ (mkPe p1 T2); ⊤ {{v,Φ v}}) ∨ (WP e @ (mkPe ∅ T1); ⊤ {{v,Φ v}})) -∗
      WP e @ (mkPe ((<[s':=F]> p1)) ((λ s vv Φ, T2 s vv Φ ∧ ⌜s <> s'⌝))); ⊤ {{v,Φ v}})%I as "Hsol";
  first (iLöb as "IH"; iIntros (Φ e) "[HWP|HWP]").
  3: {
    iIntros (s vv Φ) "[Hspec|(-> & Hspec)]".
    - iApply "Hsol". iLeft. iApply ("Hp1" with "Hspec").
    - iApply "Hsol". iRight. iApply ("Hp2" with "Hspec"). }
  1-2: rewrite !wp_unfold /wp_pre /=;
       iIntros "%σ %ns Hσ"; iSpecialize ("HWP" $! σ ns with "Hσ");
       iMod "HWP" as "[(%x & -> & Hσ & H)|[(%s & %vv & %K & -> & %H2 & >(%Ξ & Hσ & HT & H3))|(%HH & H3)]]".
  - iModIntro. iLeft. iExists x. iFrame. done.
  - destruct (decide (s=s')) as [<-|Hne].
    + 

  2: {
    iIntros (s vv Φ) "[Hspec|(-> & Hspec)]".
    - iApply "Hsol". iLeft. iApply ("Hp1" with "Hspec").
    - iApply "Hsol". iRight. iApply ("Hp2" with "Hspec").
    }
  
    *)

Lemma reducible_no_threads_mono p1 p2 e σ : p1 ⊆ p2 -> reducible_no_threads p1 e σ -> reducible_no_threads p2 e σ.
Proof.
  intros Hsub (e2 & σ2 & (K & e1' & e2' & -> & -> & H)%prim_step_inv).
  exists (fill K e2'), σ2. econstructor; first done. 1:done.
  destruct (to_class e1') as [[]|] eqn:Heq.
  - exfalso. eapply val_head_step. apply of_to_class in Heq. erewrite Heq. done.
  - apply of_to_class in Heq. subst e1'. apply call_head_step in H.
    destruct H as (Fn & HFn & Happly & -> & _).
    apply call_head_step. exists Fn. repeat split; try done.
    eapply lookup_weaken; done. 
  - eapply head_step_no_call; done. 
Qed.

Lemma link_progs T1 T2 T3 (p1 p2 : gmap string (Λ.(func))) :
    ⌜dom p1 ## dom p2⌝
 -∗ □(∀ s vv Φ, T3 s vv Φ -∗ ⌜s ∉ dom p1⌝ ∗ ⌜s ∉ dom p2⌝)
 -∗ □(spec_union T2 T3 |- p1 :: T1)
 -∗ □(spec_union T1 T3 |- p2 :: T2)
 -∗ T3 |- (union_with (fun a b => None) p1 p2) :: (spec_union T1 T2).
Proof.
  iIntros (Hdis) "#HT3 #Hp1 #Hp2".
  iAssert (∀ e Φ,
    WP e @ mkPe p1 (spec_union T2 T3); ⊤ {{ v, Φ v }} ∨ WP e @ mkPe p2 (spec_union T1 T3); ⊤ {{ v, Φ v }} -∗
    WP e @ mkPe (union_with (λ _ _ : func Λ, None) p1 p2) (T3); ⊤ {{ v, Φ v }}
    )%I as "Hen".
  + iLöb as "IHe". iIntros (e Φ).
    rewrite !wp_unfold /wp_pre /=.
    iIntros "[H|H] %σ %ns Hσ".
    - iSpecialize ("H" $! σ ns with "Hσ").
      iMod "H".
      iDestruct "H" as "[(%x & -> & Hσ & H)|[(%s' & %vv' & %K & %HeqK & %H2 & >(%Ξ & Hσ & [HT|HT] & H3))|(%HH & H3)]]".
      * iModIntro. iLeft. iExists _. iFrame. iPureIntro. done.
      * destruct (p2 !! s') as [v|] eqn:Heqp2.
        ++ iRight. iRight.
           iPoseProof ("Hp2" $! _ _ _ with "HT") as "(%HNone & HT)".
           rewrite wp_unfold /wp_pre /=.
           iSpecialize ("HT" $! σ ns with "Hσ").
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
              destruct Hstep as (Fn & Heqp2' & He2' & -> & _ ).
              iModIntro. iSplit; first iPureIntro.
              { do 2 eexists. rewrite HeqK. econstructor; first done. 1:done.
                apply call_head_step. exists Fn. repeat split; try done.
                rewrite lookup_union_with. rewrite Heqp2'. rewrite H2. done. }
              subst e. iIntros (? ? (e'2 & -> & (Fn3 & Heqp3' & He3' & -> & _ )%call_head_step)%head_reducible_prim_step_ctx).
              2: { do 3 eexists.
                   apply call_head_step. exists Fn. repeat split; try done.
                   rewrite lookup_union_with. rewrite Heqp2'. rewrite H2. done. }
              rewrite lookup_union_with in Heqp3'. rewrite Heqp2' in Heqp3'. rewrite H2 in Heqp3'.
              cbn in Heqp3'. iSpecialize ("H3'" $! σ e2').
              assert (prim_step p2 (of_class Λ (ExprCall s' vv')) σ e2' σ []) as Hstep2.
              { apply head_prim_step. apply call_head_step. eexists; repeat split; done. }
              iSpecialize ("H3'" $! Hstep2). iMod "H3'". iModIntro. iNext.
              iMod "H3'" as "(? & H3')". iModIntro. iFrame.
              iApply wp_bind. iApply (wp_wand with "[H3']").
              { iApply "IHe"; iRight. assert (e'2 = e2') as -> by congruence. iApply "H3'". }
              iIntros (r) "Hr". iSpecialize ("H3" $! r with "Hr"). iApply "IHe". iLeft. done.
        ++ iRight. iLeft. iModIntro.
           rewrite HeqK. do 3 iExists _. iSplitR; first done.
           iSplitR.
           { iPureIntro. rewrite lookup_union_with. rewrite H2. rewrite Heqp2. done. }
           iDestruct ("Hp2" with "HT") as "(%HNone2 & _)". congruence.
      * iRight. iLeft. iModIntro. do 3 iExists _; iSplitR; first done.
        rewrite lookup_union_with. rewrite H2. destruct (p2!!s') eqn:Heq.
        1: { iDestruct ("HT3" with "HT") as "(%Hne1 & %Hne2)".
             exfalso. apply Hne2. apply elem_of_dom. by eexists. }
        cbn. iSplitR; first done. iModIntro. iExists Ξ. iFrame. iNext.
        iIntros (r) "Hr". iSpecialize ("H3" with "Hr"). iApply "IHe". iLeft. done.
      * iModIntro. iRight. iRight.
        iSplitR.
        { iPureIntro. eapply reducible_no_threads_mono; last done.
          intros k. rewrite lookup_union_with. destruct (p1 !! k) as [f1|] eqn:Heq1;
          destruct (p2 !! k) as [f2|] eqn:Heq2.
          2-4: done. 
          cbn. apply elem_of_disjoint in Hdis. eapply Hdis; apply elem_of_dom; eexists; done. }
        iIntros (σ' e' Hstep%prim_step_inv).
        iSpecialize ("H3" $! σ' e').
        destruct Hstep as (K & e1' & e2' & -> & -> & H).
        assert (prim_step p1 (fill K e1') σ (fill K e2') σ' []) as Hstep.
        { econstructor. 1-2:done. destruct (to_class e1') as [[]|] eqn:Heq.
          - exfalso. eapply val_head_step. apply of_to_class in Heq. erewrite Heq. done.
          - apply of_to_class in Heq. subst e1'.
            destruct HH as (? & σ'2 & (e2'' & -> & (K2 & eK1 & eK2 & Heq1 & -> & HHstep)%prim_step_inv)%fill_step_inv).
            2: unfold to_val; by rewrite to_of_class.
            assert (K2 = empty_ectx) as ->.
            1: { destruct (fill_class' K2 eK1) as [|[vv Hvv]].
                 1: eexists; rewrite <- Heq1; by rewrite to_of_class.
                 1: done.
                 exfalso. apply of_to_class in Hvv. subst eK1. eapply val_head_step. done. }
            rewrite fill_empty in Heq1. subst eK1. apply call_head_step in H, HHstep.
            destruct H as (FN1 & HFN1 &Happy1 & -> & _).
            destruct HHstep as (FN2 & HFN2 &Happy2 & -> & _).
            rewrite lookup_union_with in HFN1. rewrite HFN2 in HFN1. destruct (p2 !! fn_name); cbn in *; try congruence.
            apply call_head_step. exists FN2. repeat split; try congruence.
          - by eapply head_step_no_call. }
        iDestruct ("H3" $! Hstep) as ">H3". iModIntro. iNext.
        iMod "H3" as "(Hσ & HWP)". iModIntro. iFrame. iApply "IHe". by iLeft.




    - iSpecialize ("H" $! σ ns with "Hσ").
      iMod "H".
      iDestruct "H" as "[(%x & -> & Hσ & H)|[(%s' & %vv' & %K & %HeqK & %H2 & >(%Ξ & Hσ & [HT|HT] & H3))|(%HH & H3)]]".
      * iModIntro. iLeft. iExists _. iFrame. iPureIntro. done.
      * destruct (p1 !! s') as [v|] eqn:Heqp2.
        ++ iRight. iRight.
           iPoseProof ("Hp1" $! _ _ _ with "HT") as "(_ & HT)".
           rewrite wp_unfold /wp_pre /=.
           iSpecialize ("HT" $! σ ns with "Hσ").
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
              destruct Hstep as (Fn & Heqp2' & He2' & -> & _ ).
              iModIntro. iSplit; first iPureIntro.
              { do 2 eexists. rewrite HeqK. econstructor; first done. 1:done.
                apply call_head_step. exists Fn. repeat split; try done.
                rewrite lookup_union_with. rewrite Heqp2'. rewrite H2. done. }
              subst e. iIntros (? ? (e'2 & -> & (Fn3 & Heqp3' & He3' & -> & _ )%call_head_step)%head_reducible_prim_step_ctx).
              2: { do 3 eexists.
                   apply call_head_step. exists Fn. repeat split; try done.
                   rewrite lookup_union_with. rewrite Heqp2'. rewrite H2. done. }
              rewrite lookup_union_with in Heqp3'. rewrite Heqp2' in Heqp3'. rewrite H2 in Heqp3'.
              cbn in Heqp3'. iSpecialize ("H3'" $! σ e2').
              assert (prim_step p1 (of_class Λ (ExprCall s' vv')) σ e2' σ []) as Hstep2.
              { apply head_prim_step. apply call_head_step. eexists; repeat split; done. }
              iSpecialize ("H3'" $! Hstep2). iMod "H3'". iModIntro. iNext.
              iMod "H3'" as "(? & H3')". iModIntro. iFrame.
              iApply wp_bind. iApply (wp_wand with "[H3']").
              { iApply "IHe"; iLeft. assert (e'2 = e2') as -> by congruence. iApply "H3'". }
              iIntros (r) "Hr". iSpecialize ("H3" $! r with "Hr"). iApply "IHe". iRight. done.
        ++ iRight. iLeft. iModIntro.
           rewrite HeqK. do 3 iExists _. iSplitR; first done.
           iSplitR.
           { iPureIntro. rewrite lookup_union_with. rewrite H2. rewrite Heqp2. done. }
           iDestruct ("Hp1" with "HT") as "(%HNone2 & _)". congruence.
      * iRight. iLeft. iModIntro. do 3 iExists _; iSplitR; first done.
        rewrite lookup_union_with. rewrite H2. destruct (p1!!s') eqn:Heq.
        1: { iDestruct ("HT3" with "HT") as "(%Hne1 & %Hne2)".
             exfalso. apply Hne1. apply elem_of_dom. by eexists. }
        cbn. iSplitR; first done. iModIntro. iExists Ξ. iFrame. iNext.
        iIntros (r) "Hr". iSpecialize ("H3" with "Hr"). iApply "IHe". iRight. done.
      * iModIntro. iRight. iRight.
        iSplitR.
        { iPureIntro. eapply reducible_no_threads_mono; last done.
          intros k. rewrite lookup_union_with. destruct (p1 !! k) as [f1|] eqn:Heq1;
          destruct (p2 !! k) as [f2|] eqn:Heq2.
          2-4: done. 
          cbn. apply elem_of_disjoint in Hdis. eapply Hdis; apply elem_of_dom; eexists; done. }
        iIntros (σ' e' Hstep%prim_step_inv).
        iSpecialize ("H3" $! σ' e').
        destruct Hstep as (K & e1' & e2' & -> & -> & H).
        assert (prim_step p2 (fill K e1') σ (fill K e2') σ' []) as Hstep.
        { econstructor. 1-2:done. destruct (to_class e1') as [[]|] eqn:Heq.
          - exfalso. eapply val_head_step. apply of_to_class in Heq. erewrite Heq. done.
          - apply of_to_class in Heq. subst e1'.
            destruct HH as (? & σ'2 & (e2'' & -> & (K2 & eK1 & eK2 & Heq1 & -> & HHstep)%prim_step_inv)%fill_step_inv).
            2: unfold to_val; by rewrite to_of_class.
            assert (K2 = empty_ectx) as ->.
            1: { destruct (fill_class' K2 eK1) as [|[vv Hvv]].
                 1: eexists; rewrite <- Heq1; by rewrite to_of_class.
                 1: done.
                 exfalso. apply of_to_class in Hvv. subst eK1. eapply val_head_step. done. }
            rewrite fill_empty in Heq1. subst eK1. apply call_head_step in H, HHstep.
            destruct H as (FN1 & HFN1 &Happy1 & -> & _).
            destruct HHstep as (FN2 & HFN2 &Happy2 & -> & _).
            rewrite lookup_union_with in HFN1. rewrite HFN2 in HFN1. destruct (p1 !! fn_name); cbn in *; try congruence.
            apply call_head_step. exists FN2. repeat split; try congruence.
          - by eapply head_step_no_call. }
        iDestruct ("H3" $! Hstep) as ">H3". iModIntro. iNext.
        iMod "H3" as "(Hσ & HWP)". iModIntro. iFrame. iApply "IHe". by iRight.


  + iIntros (s vv Φ) "[H|H]".
    - iDestruct ("Hp1" with "H") as "(%HNone & HH)".
      destruct (p2 !! s) eqn:Heq.
      * exfalso. pose proof (elem_of_disjoint (dom p1) (dom p2)) as [Hdis2 _].
        destruct (p1 !! s) eqn:Heqq; try congruence.
        eapply Hdis2; first done.
        all: apply elem_of_dom; eexists; try done. 
      * iSplitR.
        -- iPureIntro. rewrite lookup_union_with. 
           rewrite Heq. destruct (p1 !! s); cbn; congruence.
        -- iApply "Hen". by iLeft.
    - iDestruct ("Hp2" with "H") as "(%HNone & HH)".
      destruct (p1 !! s) eqn:Heq.
      * exfalso. pose proof (elem_of_disjoint (dom p1) (dom p2)) as [Hdis2 _].
        destruct (p2 !! s) eqn:Heqq; try congruence.
        eapply Hdis2; first done.
        all: apply elem_of_dom; eexists; try done. 
      * iSplitR.
        -- iPureIntro. rewrite lookup_union_with. 
           rewrite Heq. destruct (p2 !! s); cbn; congruence.
        -- iApply "Hen". by iRight.

Qed.


End wp.