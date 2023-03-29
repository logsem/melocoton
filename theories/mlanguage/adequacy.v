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
  Context {Λ : mlanguage val}.
  Context {Σ : gFunctors}.

  Context {Φpure : val → state Λ → Prop}.
  Context {pe : prog_environ Λ Σ}.
  Context {Φbi : val → iProp Σ}.

  Notation step := (prim_step (penv_prog pe)).
  Notation cfg := (prod (expr Λ) (state Λ)).

  Implicit Types σ : state Λ.
  Implicit Types v : val.
  Implicit Types e : expr Λ.
  Implicit Types X : cfg → Prop.



  Section GenAdequacy.
    Context `{!mlangG val Λ Σ}.
    (* XXX this can be strengthened to allow opening invariants (without needing to close them again annoyingly) *)
    Hypothesis HΦ : (⊢ ∀ σ v, state_interp σ ∗ Φbi v ==∗ ⌜Φpure v σ⌝).
    Hypothesis Hpeclosed : (⊢ ∀ f s vv, penv_proto pe f s vv -∗ False).

    Context {sat_at : coPset → iProp Σ → Prop}.
    Context `{!invG Σ}.
    Context `{!SatisfiableAt sat_at}.
    Context `{SatisfiableAtExists (cfg→Prop) sat_at}.

    Lemma value_from_wp σ v E :
      sat_at E (state_interp σ ∗ WP (of_val Λ v) @ pe; E {{Φbi}})%I
    → Φpure v σ.
    Proof using All.
      intros Hsat. eapply sat_mono in Hsat.
      2: {
        iIntros "(Hσ&HWP)".
        rewrite wp_unfold /wp_pre.
        iPoseProof ("HWP" $! σ with "Hσ") as "HWP". iAccu. }
      eapply sat_fupd, sat_mono in Hsat.
      2: { iIntros "[(%z & %HH & H)|[(%s & %vv & %K & %is_call & H2 & Hb & Hσ & (%Ξ & Hprot & _))|(%Hnv&_)]]".
        - apply of_val_inj in HH. subst z.
          iPoseProof (HΦ $! σ v with "H") as "H". iAccu.
        - iExFalso. iApply Hpeclosed. iApply "Hprot".
        - by rewrite to_of_val in Hnv. }
      by eapply sat_bupd, sat_elim in Hsat.
    Qed.

    Lemma one_step_from_wp σ e E:
      (to_val e = None) →
      sat_at E (state_interp σ ∗ WP e @ pe; E {{Φbi}})%I →
      ∃ X, step (e,σ) X ∧ ∀ e' σ', X (e', σ') → sat_at E (state_interp σ' ∗ WP e' @ pe; E {{Φbi}}).
    Proof using All.
      intros Hnv Hsat.
      eapply sat_mono in Hsat.
      2: {
        iIntros "(Hσ&HWP)".
        rewrite wp_unfold /wp_pre.
        iPoseProof ("HWP" $! σ with "Hσ") as "HWP". iAccu. }
      eapply sat_fupd, sat_mono in Hsat.
      2: { iIntros "[(%z & %HH & H)|[(%s & %vv & %K & %is_call & H2 & Hb & Hσ & (%Ξ & Hprot & _))|(_&H3)]]".
        - subst e. by rewrite to_of_val in Hnv.
        - iExFalso. iApply Hpeclosed. iApply "Hprot".
        - iAccu. }
      eapply sat_exists in Hsat. destruct Hsat as (X&(Hstep%sat_elim&Hsat)%sat_sep).
      exists X; split; first done.
      intros e' σ' Hcfg'.
      eapply (sat_forall e'), (sat_forall σ'), sat_wand in Hsat.
      2: iIntros "_"; by iPureIntro.
      eapply sat_fupd, sat_later, sat_fupd in Hsat. done.
    Qed.

    Lemma star_step_from_wp σ e E X:
      sat_at E (state_interp σ ∗ WP e @ pe; E {{Φbi}})%I →
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

    CoInductive star_mrel_w {A} (M : umrel A) : A → (A → Prop) → Prop :=
    | star_refl_w x (X : A → Prop) :
      X x → star_mrel_w M x X
    | star_step_w x Y (X : A → Prop) :
      M x Y →
      (∀ y, Y y → star_mrel_w M y X) →
      star_mrel_w M x X.

    Lemma star_step_from_wp_coind σ e E:
      sat_at E (state_interp σ ∗ WP e @ pe; E {{Φbi}})%I →
      (star_mrel_w step (e, σ) (λ '(e, σ), match to_val e with Some v => Φpure v σ | _ => False end)).
    Proof using All.
      revert e σ. cofix IH.
      intros e σ Hsat.
      destruct (to_val e) as [v|] eqn:Heq.
      - eapply star_refl_w. eapply of_to_val in Heq; subst e.
        rewrite to_of_val. by eapply value_from_wp.
      - eapply one_step_from_wp in Hsat; last done.
        destruct Hsat as (Y&HstepY&Hcont).
        eapply star_step_w. 1: exact HstepY.
        intros [e' σ'] Hy. eapply IH, Hcont, Hy.
    Qed.

  End GenAdequacy.

  Section ConreteAdequacy.
    Context `{!invPreG Σ}.

    (* XXX this is definitely wrong, but how to set it up properly? *)
    Lemma final_adequacy σ e E X:
      (Alloc (mlangG val Λ Σ) (λ H, state_interp σ) (invG Σ)) →
      (⊢(∀ (Hinv : invG Σ) (Hmlang : mlangG val Λ Σ) σ v, state_interp σ ∗ Φbi v ==∗ ⌜Φpure v σ⌝))%I →
      (⊢(∀ (Hinv : invG Σ) (Hmlang : mlangG val Λ Σ) f s vv, penv_proto pe f s vv -∗ False))%I →
      (⊢(∀ (Hinv : invG Σ) (Hmlang : mlangG val Λ Σ), |==> WP e @ pe ; E {{Φbi}})%I) →
      (star_AD step (e, σ) X) →
      (∃ e σ, X (e, σ) ∧ (∀ v, to_val e = Some v → Φpure v σ)).
    Proof using All.
      intros Halloc Hpure Hproto HWP Hstep.
      pose proof (@alloc_intro _ Σ) as Hsat.
      eapply alloc_wsat_inst in Hsat as (HinvG & Hsat); last done.
      eapply Halloc in Hsat as (HΛG & Hsat); last done.
      eapply alloc_iProp_sat in Hsat.
      unshelve eapply (@star_step_from_wp _ _ _ iProp_sat_at).
      1: iApply Hpure.
      1: iApply Hproto.
      7: exact Hstep.
      4: eapply sat_bupd, sat_frame_move, sat_sat_frame, sat_mono; last exact Hsat.
      1: exact ⊤.
      1-2: apply _.
      iIntros "((_&$&$)&$)". iMod (HWP $! HinvG HΛG) as "H1"; iModIntro.
      iApply wp_mask_mono; last first.
      all: done.
    Qed. 
(*Locate Alloc.
Print Alloc. Check mlangG.
Check Alloc (mlangG val Λ Σ) (λ HGS, state_interp σ ∗ WP ∗ the other two assumptions) True.
*)
  End ConreteAdequacy.
End Adequacy.





