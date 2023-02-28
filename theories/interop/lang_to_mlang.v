From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.interop Require Import linking.
From melocoton.language Require Import language.

Section ToMlang.
  Context {val : Type}.
  Context (Λ : language val).

  Local Notation prog := (gmap string Λ.(func)).
  Local Notation expr_state := ((Λ.(expr) * Λ.(state)))%type.

  Inductive may_block : Λ.(expr) → Prop := 
    BlockOnVal v : may_block (Λ.(of_class) (ExprVal v)).

  Inductive head_step_mrel : prog -> expr_state -> (expr_state->Prop) -> Prop := 
    WrapLiftS p e1 σ1 e2 σ2 (Y : _ → Prop) : 
        Λ.(head_step) p e1 σ1 e2 σ2 [] → 
        (Y (e2, σ2)) →
        head_step_mrel p (e1,σ1) Y
    (* Not reducing when not a value is UB *)
  | WrapStuckS p e σ Y :
        (¬ reducible_no_threads p e σ) →
        (¬ may_block e) →
        head_step_mrel p (e,σ) Y.

  Program Definition head_step (p : prog) : umrel (expr_state) :=
    {| mrel := head_step_mrel p |}.
  Next Obligation.
    intros p. intros [e1 σ1] X Y Hstep HXY. inversion Hstep; subst.
    + eapply (WrapLiftS p e1 σ1 e2 σ2 Y); first done. by apply HXY. 
    + eapply WrapStuckS; done.
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

  Inductive lang_to_mlang_split_state : Λ.(state) → Λ.(state) → unit → Prop :=
    split_state_refl σ : lang_to_mlang_split_state σ σ ().

  Global Program Instance lang_to_mlang_linkable : linkable lang_to_mlang Λ.(state) := {
    linking.private_state := unit;
    linking.split_state := lang_to_mlang_split_state;
  }.
  Next Obligation. intros *. inversion 1; inversion 1; by simplify_eq. Qed.

End ToMlang.
