From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.interop Require Import lang_to_mlang.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
(* From melocoton.interop Require Import linking_wp. *)
From iris.proofmode Require Import proofmode.

Section ToMlang_logic.
Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context {val : Type}.
Context (Λ: language val).
Context `{!language.weakestpre.langGS val Λ Σ, !invGS_gen hlc Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types T : string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ.

Global Program Instance lang_to_mlang_mlangGS :
  mlanguage.weakestpre.mlangGS val Σ (lang_to_mlang Λ)
:= {
  state_interp := (λ σ, ∃ n, language.weakestpre.state_interp σ n)%I;
  at_boundary := True%I;
}.

(*

Global Program Instance lang_to_mlang_linkableGS :
  (@linkableGS _ _ (lang_to_mlang Λ) _ _ (lang_to_mlang_linkable Λ) state_interp)%I
:= {
  private_state_interp := (λ _, True)%I;
}. 
Next Obligation. simpl. intros *. inversion 1. iIntros "?". by iFrame. Qed.
Next Obligation.
  simpl. intros ? []. iIntros "? _". iModIntro. iExists _. by iFrame.
Qed.
Next Obligation. simpl. iIntros (σ) "_ Hσ". iPureIntro. exists σ, (). constructor. Qed.
*)
(* This is a *local* instance to allow typechecking the lemma below. The idea is
   that it should stay local. For each specific language, one should manually
   define the corresponding mlanguage (by applying lang_to_mlang), and define it
   there as a canonical structure. *)
Local Canonical Structure lang_to_mlang_mlang : mlanguage val := lang_to_mlang Λ.

Notation mkPE p T := (@Build_prog_environ _ _ _ p T).

Definition penv_to_mlang (pe : language.weakestpre.prog_environ Λ Σ) :
  mlanguage.weakestpre.prog_environ (lang_to_mlang Λ) Σ
:=
  {| penv_prog := pe.(language.weakestpre.penv_prog);
     penv_proto := pe.(language.weakestpre.penv_proto) |}.

Lemma wp_lang_to_mlang (e : Λ.(language.expr)) pe E Φ :
  ⊢ WP e @ pe; E {{ Φ }} -∗ WP e @ (penv_to_mlang pe); E {{ Φ }}.
Proof using.
  iStartProof. iLöb as "IH" forall (e). destruct pe as [p T].
  rewrite {1} @language.weakestpre.wp_unfold /language.weakestpre.wp_pre. simpl.
  rewrite {1} wp_unfold /mlanguage.weakestpre.wp_pre.
  iIntros "H" (σ) "(%n & Hσ)". iMod ("H" $! σ n with "Hσ") as "[(%x & %H1 & Hσ & H)|[(%s' & %vv & %K' & %H1 & %H2 & H3)|(%Hred & H3)]]"; cbn.
  - iLeft. iModIntro. iExists x. iFrame. iSplitR; first done. iExists n. iFrame.
  - iRight. iLeft. iMod "H3" as "(%Ξ & Hσ & HT & Hr)". iExists s', vv, K'. iModIntro.
    iSplitR; first done. iSplitR; first done. iSplitR; first done. iSplitL "Hσ"; first by iExists n.
    iExists Ξ. iFrame. iNext. iIntros (v) "[Hv _]". iApply "IH". by iApply "Hr".
  - iRight. iRight. iModIntro. iSplitR.
    { iPureIntro. eapply reducible_not_val. done. }
    iIntros (X Hstep). inversion Hstep; simplify_eq.
    + iMod ("H3" $! σ2 e2 H3) as "H3". do 2 iModIntro. iMod "H3" as "(Hσ&HWP)". iModIntro. 
      do 2 iExists _; iSplit; first done.
      iSplitL "Hσ"; first by iExists _.
      iApply "IH". done.
    + destruct H4 as [_ H4%not_reducible]. exfalso; tauto.
Qed.

Lemma wp_lang_to_mlang_backwards (e : Λ.(language.expr)) pe E Φ :
  ⊢ WP e @ (penv_to_mlang pe); E {{ Φ }} -∗ WP e @ pe; E {{ Φ }}.
Proof using.
  iStartProof. iLöb as "IH" forall (e). destruct pe as [p T].
  rewrite {1} @language.weakestpre.wp_unfold /language.weakestpre.wp_pre. simpl.
  rewrite {1} wp_unfold /mlanguage.weakestpre.wp_pre.
  iIntros "H" (σ n) "Hσ".
  iMod ("H" $! σ with "[Hσ]") as "[(%x & %H1 & Hσ & H)|[(%s' & %vv & %K' & %Hcall & %H2 & _ & (%n0 & Hσ) & H3)|(%Hred & H3)]]"; cbn.
  - iExists n; done.
  - iLeft. iModIntro. iExists x. iFrame. iSplitR; first done. iDestruct "Hσ" as "(%&HH)".
    assert (n = n0) as -> by admit. done.
  - iRight. iLeft. cbn in Hcall. unfold lang_to_mlang.is_call in Hcall. subst e.
    iModIntro. do 3 iExists _; iSplit; first done.
    iSplit; first done.
    iPoseProof "H3" as "(%Ξ & HT & Hr)". iModIntro. iExists Ξ.
    assert (n = n0) as -> by admit. iFrame.
    iNext. iIntros (v) "Hv". iApply "IH". iApply "Hr". iFrame.
  - iRight. iRight. iModIntro.
    eapply (prim_step_is_total p e σ) in Hred as Hstep.
    inversion Hstep; simplify_eq.
    2: { iPoseProof ("H3" $! (λ _, False) (LiftUbStep _ p e σ _ H4)) as "H3".
         iAssert (|={E}▷=> False)%I with "[H3]" as "Halmost_false".
         1: iMod "H3"; do 2 iModIntro; iMod "H3" as "(%&%&[]&_)".
         Fail iApply "Halmost_false". admit. }
    iSplit.
    1: iPureIntro; by do 2 eexists.
    iIntros (σ3 e3 Hstep2).
    assert (prim_step p (e, σ) (λ '(e4,σ4), e4=e3 ∧ σ4=σ3)) as HstepW.
    1: eapply LiftStep; done.
    iMod ("H3" $! _ HstepW) as "H3". do 2 iModIntro.
    iMod "H3" as "(%e4&%σ4&(->&->)&(%n0&Hσ)&HWP)". iModIntro.
    assert (S n = n0) as -> by admit. iFrame.
    iApply "IH". done.
Abort.


Lemma wp_lang_to_mlang_bind K pe E e Φ :
  WP e @ (penv_to_mlang pe); E {{ v, WP fill K (of_class _ (ExprVal v)) @ (penv_to_mlang pe); E {{ Φ }} }} ⊢ WP fill K e @ (penv_to_mlang pe); E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre.
  iIntros "%σ Hσ".
  iMod ("H" $! σ with "Hσ") as "[(%x & -> & Hσ & H)|[(%s & %vv & %K' & %HH & %H2 & Hb & Hσ & %Ξ & HT & Hr)|(%Hnv&H3)]]".
  - rewrite {1} wp_unfold /wp_pre.
    iMod ("H" $! σ with "Hσ") as "H". iModIntro. iApply "H".
  - iModIntro. iRight. iLeft. iExists s, vv, (comp_ectx K K').
    rewrite /is_call /= /lang_to_mlang.is_call in HH; subst e.
    iSplitR; first by erewrite (fill_comp K K').
    iSplitR; first done. iFrame.
    iExists Ξ. iFrame. iNext.
    iIntros "%r HΞ". rewrite /resume_with /=.
    rewrite <- fill_comp.
    iApply "IH". iApply ("Hr" with "HΞ").
  - iRight. iRight. iModIntro. iSplit. 
    1: iPureIntro; by apply fill_not_val.
    iIntros (X Hstep). inversion Hstep; simplify_eq.
    + eapply fill_step_inv in H3 as (e2'&->&Hstep'); last done.
      assert (prim_step (penv_prog (penv_to_mlang pe)) (e, σ) (λ '(e4,σ4), e4=e2' ∧ σ4=σ2)) as HstepW.
      1: eapply LiftStep; done.
      iMod ("H3" $! _ HstepW) as "H3". do 2 iModIntro.
      iMod "H3" as "(%e4&%σ4&(->&->)&(%n0&Hσ)&HWP)". iModIntro.
      do 2 iExists _. iSplit; first done.
      iSplitL "Hσ"; first by iExists _. iApply "IH". done.
    + destruct H4 as [Hnvf Hst].
      assert (stuck (penv_prog (penv_to_mlang pe)) e σ) as Hirred.
      { split; first done. intros ? ? ?. eapply (Hst (fill K e') σ').
        eapply fill_prim_step. done. }
      iMod ("H3" $! (λ _, False) (LiftUbStep _ _ _ _ _ Hirred)) as "H3".
      do 2 iModIntro. iMod "H3" as "(%&%&[]&_)".
Qed.

End ToMlang_logic.

Global Arguments penv_to_mlang {_ _ _} _.
