From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.lang_to_mlang Require Import lang.
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
  state_interp := language.weakestpre.state_interp;
  at_boundary := True%I;
}.

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

(* This is a *local* instance to allow typechecking the lemma below. The idea is
   that it should stay local. For each specific language, one should manually
   define the corresponding mlanguage (by applying lang_to_mlang), and define it
   there as a canonical structure. *)
Local Canonical Structure lang_to_mlang_mlang : mlanguage val := lang_to_mlang Λ.

Definition penv_to_mlang (pe : language.progenv.prog_environ Λ Σ) :
  mlanguage.progenv.prog_environ (lang_to_mlang Λ) Σ
:= ⟪ pe.(language.progenv.penv_prog), pe.(language.progenv.penv_proto) ⟫.

Lemma wp_lang_to_mlang (e : Λ.(language.expr)) pe E Φ :
  ⊢ WP e @ pe; E {{ Φ }} -∗ WP e @ (penv_to_mlang pe); E {{ Φ }}.
Proof using.
  iStartProof. iLöb as "IH" forall (e). destruct pe as [p T].
  rewrite {1} @language.weakestpre.wp_unfold /language.weakestpre.wp_pre. simpl.
  rewrite {1} wp_unfold /mlanguage.weakestpre.wp_pre.
  iIntros "H" (σ) "Hσ". iMod ("H" $! σ with "Hσ") as "[(%x & %H1 & Hσ & H)|[(%s' & %vv & %K' & %H1 & %H2 & H3)|(%Hred & H3)]]"; cbn.
  - iLeft. iModIntro. iExists x. by iFrame.
  - iRight. iLeft. iMod "H3" as "(%Ξ & Hσ & HT & Hr)". iExists s', vv, K'. iModIntro.
    iSplitR; first done. iSplitR; first done. iSplitR; first done. iFrame.
    iExists Ξ. iFrame. iNext. iIntros (v) "[Hv _]". iApply "IH". by iApply "Hr".
  - iRight. iRight. iModIntro. iSplitR.
    { iPureIntro. eapply reducible_not_val. done. } iSplitR.
    { iPureIntro. intros (f&vs&C&->&Hno).
      eapply reducible_call_is_in_prog; try done.
      by rewrite /to_call to_of_class. }
    iIntros (X Hstep). inversion Hstep; simplify_eq.
    destruct H5 as (e2&σ2&Hstep'&HX). 1: done.
    iMod ("H3" $! σ2 e2 Hstep') as "H3". do 2 iModIntro. iMod "H3" as "(Hσ&HWP)". iModIntro. 
    do 2 iExists _; iSplit; first done. iFrame.
    by iApply "IH".
Qed.

(*
Lemma wp_lang_to_mlang_backwards (e : Λ.(language.expr)) pe E Φ :
  ⊢ WP e @ (penv_to_mlang pe); E {{ Φ }} -∗ WP e @ pe; E {{ Φ }}.
Proof using.
  iStartProof. iLöb as "IH" forall (e). destruct pe as [p T].
  rewrite {1} @language.weakestpre.wp_unfold /language.weakestpre.wp_pre. simpl.
  rewrite {1} wp_unfold /mlanguage.weakestpre.wp_pre.
  iIntros "H" (σ) "Hσ".
  iMod ("H" $! σ with "[Hσ]") as "[(%x & -> & Hσ & H)|[(%s' & %vv & %K' & %Hcall & %H2 & _ & Hσ & H3)|(%Hred & %Hext & H3)]]"; cbn.
  - done.
  - iLeft. iModIntro. iExists x. iFrame. done.
  - iRight. iLeft. cbn in Hcall. unfold lang_to_mlang.is_call in Hcall. subst e.
    iModIntro. do 3 iExists _; iSplit; first done.
    iSplit; first done.
    iPoseProof "H3" as "(%Ξ & HT & Hr)". iModIntro. iExists Ξ. iFrame.
    iNext. iIntros (v) "Hv". iApply "IH". iApply "Hr". iFrame.
  - iRight. iRight. iModIntro.
    iSplit. {
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

*)

End ToMlang_logic.

Global Arguments penv_to_mlang {_ _ _} _.
