From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.interop Require Import lang_to_mlang.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From iris.proofmode Require Import proofmode.


Section Embed_logic.
Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context {val : Type}.
Context (Λ: language val).
Context `{!language.weakestpre.melocotonGS_gen hlc val Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types v : val.
Implicit Types T : string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ.

Instance language_publicStateInterp :
  mlanguage.weakestpre.publicStateInterp (language.state Λ) Σ
:= {
  public_state_interp := (λ σ, ∃ n, language.weakestpre.state_interp σ n)%I
}.

Program Instance embed_mlangGS :
  mlanguage.weakestpre.mlangGS hlc val Λ.(language.state) Σ (embed_lang Λ)
:= {
  state_interp := (λ σ, ∃ n, language.weakestpre.state_interp σ n)%I;
  private_state_interp := (λ _, True)%I;
}.
Next Obligation. simpl. intros *. inversion 1. iIntros "?". by iFrame. Qed.
Next Obligation. simpl. intros *. inversion 1; subst. iIntros "[? _]". by iFrame. Qed.

Definition lang_prog_environ p T : language.weakestpre.prog_environ :=
   language.weakestpre.Build_prog_environ hlc _ _ _ _ p T.
Definition mlang_prog_environ p T : mlanguage.weakestpre.prog_environ :=
   mlanguage.weakestpre.Build_prog_environ hlc _ _ _ _ _ _ _ p T.

Lemma wp_embed e p T E Φ :
  ⊢ WP e @ lang_prog_environ p T ; E {{v, Φ v}} -∗ WP e @ mlang_prog_environ p T ; E {{v, Φ v}}.
Proof using.
  iStartProof. iLöb as "IH" forall (e).
  rewrite {1} @language.weakestpre.wp_unfold /language.weakestpre.wp_pre.
  rewrite {1} wp_unfold /wp_pre.
  iIntros "H" (σ) "((%n & Hσ) & _)". iMod ("H" $! σ n with "Hσ") as "[(%x & %H1 & Hσ & H)|[(%s' & %vv & %K' & %H1 & %H2 & H3)|(%Hred & H3)]]".
  - iLeft. iModIntro. iExists x. iFrame. iSplitR; first done. iExists n. iFrame.
  - iRight. iLeft. iMod "H3" as "(%Ξ & Hσ & HT & Hr)". iExists s', vv, K'. iModIntro.
    iSplitR; first done. iSplitR; first done. iModIntro. iSplitL "Hσ"; first by iExists n.
    iExists Ξ. iFrame.
    iNext. iIntros (v) "Hv". iApply "IH". by iApply "Hr".
  - iRight. iRight. iModIntro. iSplitR.
    { iPureIntro. destruct Hred as (e' & σ' & H'). eexists (fun '(e2,σ2) => e2 = e' ∧ σ2 = σ'). inversion H'; subst. econstructor. eexists; split; first done. econstructor; first done. intros ? ? ( <- & <- ); done. }
    iIntros (X Hstep). inversion Hstep as (K & e' & -> & Hx). inversion Hx; subst.
    unshelve iMod ("H3" $! σ2 _ (Prim_step _ K _ _ _ _ _ _ _ _ _ H3)) as "H3". 1-2:done.
    do 2 iModIntro. iMod "H3" as "(Hσ & Hwp)". iModIntro. iExists _, _. iSplitR; first (iPureIntro; apply H5; repeat split).
    iSplitL "Hσ"; first by iExists _. iApply "IH". iApply "Hwp".
Qed.

End Embed_logic.
