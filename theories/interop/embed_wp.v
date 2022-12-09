From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.interop Require Import lang_to_mlang.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import linking_wp.
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

Global Program Instance embed_mlangGS :
  mlanguage.weakestpre.mlangGS hlc val Σ (lang_to_mlang Λ)
:= {
  state_interp := (λ σ, ∃ n, language.weakestpre.state_interp σ n)%I;
  at_boundary := True%I;
}.

Global Program Instance embed_linkableGS :
  (@linkableGS _ _ _ (lang_to_mlang Λ) _ _ (embed_linkable Λ) state_interp)%I
:= {
  private_state_interp := (λ _, True)%I;
}.
Next Obligation. simpl. intros *. inversion 1. iIntros "?". by iFrame. Qed.
Next Obligation.
  simpl. intros ? []. iIntros "? _". iModIntro. iExists _. by iFrame.
Qed.
Next Obligation. simpl. iIntros (σ) "_ Hσ". iPureIntro. exists σ, (). constructor. Qed.


Local Canonical Structure embed_mlang : mlanguage val := lang_to_mlang Λ.

Definition penv_to_mlang (pe : language.weakestpre.prog_environ Λ Σ) :
  mlanguage.weakestpre.prog_environ (lang_to_mlang Λ) Σ
:=
  {| penv_prog := pe.(language.weakestpre.penv_prog);
     penv_proto := pe.(language.weakestpre.penv_proto) |}.

Lemma wp_embed (e : Λ.(language.expr)) pe E Φ :
  ⊢ WP e @ pe; E {{ Φ }} -∗ WP e @ (penv_to_mlang pe); E {{ Φ }}.
Proof using.
  iStartProof. iLöb as "IH" forall (e). destruct pe as [p T].
  rewrite {1} @language.weakestpre.wp_unfold /language.weakestpre.wp_pre. simpl.
  rewrite {1} wp_unfold /mlanguage.weakestpre.wp_pre.
  iIntros "H" (σ) "(%n & Hσ)". iMod ("H" $! σ n with "Hσ") as "[(%x & %H1 & Hσ & H)|[(%s' & %vv & %K' & %H1 & %H2 & H3)|(%Hred & H3)]]".
  - iLeft. iModIntro. iExists x. iFrame. iSplitR; first done. iExists n. iFrame.
  - iRight. iLeft. iMod "H3" as "(%Ξ & Hσ & HT & Hr)". iExists s', vv, K'. iModIntro.
    iSplitR; first done. iSplitR; first done. iSplitR; first done. iSplitL "Hσ"; first by iExists n.
    iExists Ξ. iFrame. iNext. iIntros (v) "[Hv _]". iApply "IH". by iApply "Hr".
  - iRight. iRight. iModIntro. iSplitR.
    { iPureIntro. destruct Hred as (e' & σ' & H'). eexists (fun '(e2,σ2) => e2 = e' ∧ σ2 = σ'). inversion H'; subst. econstructor. eexists; split; first done.
      econstructor; first done. intros ? ? ( <- & <- ); done. }
    iIntros (X Hstep). inversion Hstep as (K & e' & -> & Hx). inversion Hx; subst.
    unshelve iMod ("H3" $! σ2 _ (Prim_step _ K _ _ _ _ _ _ _ _ _ H3)) as "H3". 1-2:done.
    do 2 iModIntro. iMod "H3" as "(Hσ & Hwp)". iModIntro. iExists _, _. iSplitR; first (iPureIntro; apply H5; repeat split).
    iSplitL "Hσ"; first by iExists _. iApply "IH". iApply "Hwp".
Qed.

End Embed_logic.

Global Arguments penv_to_mlang {_ _ _} _.
