From iris.proofmode Require Import base proofmode classes.
From transfinite.base_logic.lib Require Export fancy_updates.
From melocoton.mlanguage Require Export mlanguage progenv weakestpre.
From melocoton Require Import multirelations named_props.
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import satisfiable.
From transfinite.stepindex Require Import ordinals.
Import uPred.
Import umrel.

Section Adequacy.
  Existing Instance ordI.
  Context {val : Type}.
  Context (Λ : mlanguage val).
  Context {Σ : gFunctors}.

  Context (Φpure : val → state Λ → Prop).
  Context (p : mlang_prog Λ).
  Context (Ψ : protocol val Σ).
  Context (Φbi : val → iProp Σ).

  Notation step := (prim_step p).
  Notation cfg := (prod (expr Λ) (state Λ)).

  Implicit Types σ : state Λ.
  Implicit Types v : val.
  Implicit Types e : expr Λ.
  Implicit Types X : cfg → Prop.

  Definition sideConds `{!invG Σ, !mlangG val Λ Σ} : iProp Σ := 
    □ (∀ σ v, state_interp σ ∗ Φbi v ==∗ ⌜Φpure v σ⌝)
  ∗ □ (∀ f s vv, penv_proto ⟪p,Ψ⟫ f s vv -∗ False).

  Section GenAdequacy.
    Context `{!mlangG val Λ Σ, !invG Σ}.
    Context (sat_at : coPset → iProp Σ → Prop).
    Context `{!SatisfiableAt sat_at}.
    Context `{SatisfiableAtExists (cfg→Prop) sat_at}.

    Lemma value_from_wp σ v E :
      sat_at E (sideConds ∗ state_interp σ ∗ WP (of_val Λ v) @ ⟪p,Ψ⟫; E {{Φbi}})%I
    → Φpure v σ.
    Proof using All.
      intros Hsat. eapply sat_mono in Hsat. 1: eapply sat_fupd, sat_elim in Hsat; eapply Hsat.
      iIntros "(#(HΦ&Hproto)&Hσ&HWP)".
      rewrite wp_unfold /wp_pre.
      iPoseProof ("HWP" $! σ with "Hσ") as "HWP".
      iMod "HWP" as "[(%z & %HH & H)|[(%s & %vv & %K & %is_call & H2 & Hb & Hσ & (%Ξ & Hprot & _))|(%Hnv&H3)]]".
      - apply of_val_inj in HH. subst z.
        iApply ("HΦ" $! σ v with "H").
      - iExFalso. iApply "Hproto". iApply "Hprot".
      - by rewrite to_of_val in Hnv.
    Qed.

    Lemma one_step_from_wp σ e E:
      (to_val e = None) →
      sat_at E (sideConds ∗ state_interp σ ∗ WP e @ ⟪p,Ψ⟫; E {{Φbi}})%I →
      ∃ X, step (e,σ) X ∧ ∀ e' σ', X (e', σ') → sat_at E (sideConds ∗ state_interp σ' ∗ WP e' @ ⟪p,Ψ⟫; E {{Φbi}}).
    Proof using All.
      intros Hnv Hsat.
      eapply sat_mono in Hsat.
      1: eapply sat_fupd, sat_exists in Hsat;
         destruct Hsat as (X&(Hstep%sat_elim & Hsat)%sat_sep).
      2: {
        iIntros "(Hsides&Hσ&HWP)".
        rewrite wp_unfold /wp_pre.
        iMod ("HWP" $! σ with "Hσ") as "[(%z & %HH & H)|[(%s & %vv & %K & %is_call & H2 & Hb & Hσ & (%Ξ & Hprot & _))|(_&%X&Hpure&H3)]]".
        - exfalso. subst e. by rewrite to_of_val in Hnv.
        - iExFalso. iDestruct "Hsides"  as "(_&Hproto)". iApply "Hproto". iApply "Hprot".
        - iModIntro. iApply (exist_intro X). iFrame; iAccu. }
      exists X; split; first done.
      intros e' σ' Hcfg'.
      eapply sat_mono in Hsat; first (eapply sat_fupd, sat_later, sat_fupd in Hsat; exact Hsat).
      iIntros "(Hside&H3)". iFrame. iMod ("H3" $! e' σ' Hcfg') as "H3".
      iModIntro. iNext. iApply "H3".
    Qed.

    Lemma star_step_from_wp σ e E X:
      sat_at E (sideConds ∗ state_interp σ ∗ WP e @ ⟪p,Ψ⟫; E {{Φbi}})%I →
      (star_AD step (e, σ) X) →
      (∃ e σ, X (e, σ) ∧ (∀ v, to_val e = Some v → Φpure v σ)).
    Proof using All.
      assert (∃ x, fst x = e ∧ snd x = σ ∧ (e,σ)=x) as (x&<-&<-&->).
      1: by exists (e,σ).
      intros Hsat. unfold mrel; cbn in *.
      induction 1 as [[e σ] X H|[e σ] X IH] in Hsat|-*; cbn in *.
      - exists e, σ. split; first done.
        intros v <-%of_to_val. by eapply value_from_wp.
      - destruct (to_val e) as [v|] eqn:Heq.
        1: eapply of_to_val in Heq; subst e;
          destruct (IH _ (val_prim_step _ _ _)) as (?&[]&_).
        eapply one_step_from_wp in Hsat; last done.
        destruct Hsat as (Y&HstepY&Hcont).
        destruct (IH Y HstepY) as ([e' σ']&Hy&Hmrel&Hsat).
        eapply Hsat, Hcont, Hy.
    Qed.

    Lemma trace_step_from_wp σ e E:
      sat_at E (sideConds ∗ state_interp σ ∗ WP e @ ⟪p,Ψ⟫; E {{Φbi}})%I →
      trace step (e, σ) (λ '(e', σ'), ∃ v, to_val e' = Some v ∧ Φpure v σ').
    Proof using All.
      revert e σ. cofix IH.
      intros e σ Hsat.
      destruct (to_val e) as [v|] eqn:Heq.
      - eapply trace_refl. eapply of_to_val in Heq; subst e.
        rewrite to_of_val. eexists; split; eauto. by eapply value_from_wp.
      - eapply one_step_from_wp in Hsat; last done.
        destruct Hsat as (Y&HstepY&Hcont).
        eapply trace_step. 1: exact HstepY.
        intros [e' σ'] Hy. eapply IH, Hcont, Hy.
    Qed.

  End GenAdequacy.


  Section ConreteAdequacy.
    Context `{!invPreG Σ}.

    Context (e : Λ.(expr)).
    Context (σ : Λ.(state)).
    Context (Halloc : ∀ `{!invG Σ}, Alloc (mlangG val Λ Σ) (λ H,
      sideConds ∗ state_interp σ ∗ WP e @ ⟪p,Ψ⟫ ; ⊤ {{Φbi}})%I True).

    Lemma alloc_adequacy X:
      star_AD step (e, σ) X →
      ∃ e σ, X (e, σ) ∧ (∀ v, to_val e = Some v → Φpure v σ).
    Proof using All.
      pose proof (@alloc_intro _ Σ) as Hsat.
      eapply alloc_wsat_inst in Hsat as (HinvG&Hsat); last done.
      eapply (Halloc HinvG) in Hsat as (HmlangG&Hsat); last done.
      eapply alloc_iProp_sat in Hsat.
      eapply (star_step_from_wp iProp_sat_at).
      unfold iProp_sat_at, sat_frame.
      eapply sat_mono; last exact Hsat.
      iIntros "((_&$)&$)".
    Qed.

    Lemma alloc_adequacy_coind :
      trace step (e, σ) (λ '(e', σ'), ∃ v, to_val e' = Some v ∧ Φpure v σ').
    Proof using All.
      pose proof (@alloc_intro _ Σ) as Hsat.
      eapply alloc_wsat_inst in Hsat as (HinvG&Hsat); last done.
      eapply (Halloc HinvG) in Hsat as (HmlangG&Hsat); last done.
      eapply alloc_iProp_sat in Hsat.
      eapply (trace_step_from_wp iProp_sat_at).
      unfold iProp_sat_at, sat_frame.
      eapply sat_mono; last exact Hsat.
      iIntros "((_&$)&$)".
    Qed.

  End ConreteAdequacy.
End Adequacy.





