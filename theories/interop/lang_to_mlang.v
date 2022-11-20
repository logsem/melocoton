From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.interop Require Import linking.
From melocoton.language Require Import language.

Section ToMLang.
  Context {val : Type}.
  Context (Λ : language val).

  Local Notation prog := (gmap string Λ.(func)).
  Local Notation expr_state := ((Λ.(expr) * Λ.(state)))%type.
  Inductive head_step_mrel : prog -> expr_state -> (expr_state->Prop) -> Prop := 
    wrap p e1 σ1 e2 σ2 (Y : _ → Prop) : Λ.(head_step) p e1 σ1 e2 σ2 [] → 
    (forall e2' σ2', e2 = e2' ∧ σ2 = σ2' → Y (e2', σ2')) → head_step_mrel p (e1,σ1) Y.

  Program Definition head_step (p : prog) : umrel (expr_state) :=
    {| mrel := head_step_mrel p |}.
  Next Obligation.
    intros p. intros [e1 σ1] X Y Hstep HXY. inversion Hstep; subst.
    eapply (wrap p e1 σ1 e2 σ2); first done. intros ? ? (<- & <-).
    apply HXY, H4. done.
  Qed.

  Lemma language_mlanguage_mixin :
    MlanguageMixin (val:=val) Λ.(of_class) Λ.(to_class) Λ.(empty_ectx) Λ.(comp_ectx) Λ.(fill)
      Λ.(apply_func) head_step.
  Proof using.
    constructor; try apply language_mixin.
    - intros p v σ H Hstep. inversion Hstep; subst. eapply val_head_step. apply H3.
    - intros p f vs σ X. split; intros H.
      + inversion H; subst. destruct (call_head_step p f vs σ e2 σ2 []) as [HL HR].
        destruct (HL H3) as (fn & Heq1 & Heq2 & Heq3 & Heq4). eexists fn, e2. repeat split; try congruence.
        apply H5. repeat split; congruence.
      + destruct H as (fn & e2 & Heq1 & Heq2 & HX).
        destruct (call_head_step p f vs σ e2 σ []) as [HL HR].
        eapply wrap. 1: apply HR; by eexists. intros ? ? ( <- & <- ). apply HX.
    - intros p K' K_redec e1 e1_redex σ X Heq1 Heq2 Hstep. inversion Hstep; subst.
      eapply step_by_val; try done. unfold to_val. destruct (to_class e1) as [[]|]; try congruence. exfalso. easy.
    - intros p K e σ X H. inversion H; subst.
      destruct (head_ctx_step_val p K e σ e2 σ2 [] H3) as [HL|[v Hv]].
      + now left.
      + right. exists v. unfold to_val in Hv. destruct (to_class e) as [[]|]; try congruence.
  Qed.

  Definition lang_to_mlang : mlanguage val :=
    Mlanguage language_mlanguage_mixin.

  Inductive embed_split_state : Λ.(state) → Λ.(state) → unit → Prop :=
    split_state_refl σ : embed_split_state σ σ ().

  Global Program Instance embed_linkable : linkable lang_to_mlang Λ.(state) := {
    linking.private_state := unit;
    linking.split_state := embed_split_state;
  }.
  Next Obligation. intros *. inversion 1; inversion 1; by simplify_eq. Qed.

End ToMLang.
