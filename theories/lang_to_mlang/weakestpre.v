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
Implicit Types T : protocol val Σ.

Global Program Instance lang_to_mlang_mlangGS :
  mlanguage.weakestpre.mlangGS val (lang_to_mlang Λ) Σ
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

Lemma wp_lang_to_mlang (e : Λ.(language.expr)) p T E Φ :
  ⊢ WP e @ ⟨p, T⟩; E {{ Φ }} -∗ WP e @ ⟪p, T⟫; E {{ Φ }}.
Proof using.
  iStartProof. iLöb as "IH" forall (e).
  rewrite {1} @language.weakestpre.wp_unfold /language.weakestpre.wp_pre. simpl.
  rewrite {1} wp_unfold /mlanguage.weakestpre.wp_pre.
  iIntros "H" (σ) "Hσ". iMod ("H" $! σ with "Hσ") as "[(%x & %H1 & Hσ & H)|[(%s' & %vv & %K' & %H1 & %H2 & H3)|(%Hred & H3)]]"; cbn.
  - iLeft. iModIntro. iExists x. by iFrame.
  - iRight. iLeft. iMod "H3" as "(%Ξ & Hσ & HT & Hr)". iExists s', vv, K'. iModIntro.
    iSplitR; first done. iSplitR; first done. iSplitR; first done. iFrame.
    iExists Ξ. iFrame. iNext. iIntros (v) "[Hv _]". iApply "IH". by iApply "Hr".
  - iRight. iRight. iModIntro. iSplitR.
    { iPureIntro. eapply reducible_not_val. done. }
    iExists (λ '(e2, σ2), language.prim_step p e σ e2 σ2).
    iSplit. { iPureIntro. by econstructor. }
    iIntros (e' σ' Hstep). iMod ("H3" $! _ _ Hstep) as "H3".
    do 2 iModIntro. iMod "H3" as "[Hσ HWP]". iModIntro.
    iFrame. by iApply "IH".
Qed.

Lemma wp_lang_to_mlang_backwards (e : Λ.(language.expr)) p Ψ E Φ :
  ⊢ WP e @ ⟪p, Ψ⟫; E {{ Φ }} -∗ WP e @ ⟨p, Ψ⟩; E {{ Φ }}.
Proof using.
  iStartProof. iLöb as "IH" forall (e).
  rewrite {1} @language.weakestpre.wp_unfold /language.weakestpre.wp_pre. simpl.
  rewrite {1} wp_unfold /mlanguage.weakestpre.wp_pre.
  iIntros "H" (σ) "Hσ".
  iMod ("H" $! σ with "[Hσ]") as "[(%x & -> & Hσ & H)|[(%s' & %vv & %K' & %Hcall & %H2 & _ & Hσ & H3)|(%Hval & %Hext & %Hstep & H3)]]"; cbn.
  - done.
  - iLeft. iModIntro. iExists x. iFrame. done.
  - iRight. iLeft. cbn in Hcall. unfold is_call in Hcall. subst e.
    iModIntro. do 3 iExists _; iSplit; first done.
    iSplit; first done.
    iPoseProof "H3" as "(%Ξ & HT & Hr)". iModIntro. iExists Ξ. iFrame.
    iNext. iIntros (v) "Hv". iApply "IH". iApply "Hr". iFrame.
  - iRight. iRight. iModIntro.
    inversion Hstep; simplify_eq.
    specialize (H3 Hval).
    iSplit; first done.
    iIntros (σ' e' Hstep').
    iMod ("H3" $! _ _ (H5 _ _ Hstep')) as "H3".
    do 2 iModIntro. iMod "H3" as "[Hσ HWP]". iModIntro.
    iFrame. by iApply "IH".
Qed.

Lemma wp_lang_to_mlang_eq e p Ψ E Φ :
  WP e @ ⟪p, Ψ⟫; E {{ Φ }} ⊣⊢ WP e @ ⟨p, Ψ⟩; E {{ Φ }}.
Proof.
  iIntros; iSplit.
  - iApply wp_lang_to_mlang_backwards.
  - iApply wp_lang_to_mlang.
Qed.

Lemma lang_to_mlang_refines E (p : lang_prog Λ) Ψ :
  prog_proto E p Ψ ⊑ mprog_proto E p Ψ.
Proof using.
  iIntros (? ? ?) "Hproto". rewrite /prog_proto /mprog_proto.
  destruct (p !! s) as [fn|] eqn:HH; rewrite HH //; [].
  iDestruct "Hproto" as (? ?) "Hwp". iExists _. iSplit; first done.
  iNext. iIntros "_". iApply (wp_wand with "[Hwp]"); first by iApply wp_lang_to_mlang.
  iIntros (?) "H". cbn. iFrame.
Qed.

Lemma lang_to_mlang_refines_rev E (p : lang_prog Λ) Ψ :
  mprog_proto E p Ψ ⊑ prog_proto E p Ψ.
Proof using.
  iIntros (? ? ?) "Hproto". rewrite /prog_proto /mprog_proto.
  destruct (p !! s) as [fn|] eqn:HH; rewrite HH //; [].
  iDestruct "Hproto" as (? ?) "Hwp". iExists _. iSplit; first done.
  iNext. iSpecialize ("Hwp" with "[]"); first done.
  iApply (language.weakestpre.wp_wand with "[Hwp]"); first by iApply wp_lang_to_mlang_backwards.
  by iIntros (?) "[H _]".
Qed.

End ToMlang_logic.
