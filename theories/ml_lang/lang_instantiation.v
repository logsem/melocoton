From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.language Require Import language.
From melocoton.ml_lang Require Export lang metatheory.

Import ML_lang.

Local Notation state := (gmap loc (option (list val))).

Local Lemma melocoton_lang_mixin_ML :
  @LanguageMixin expr val ml_function (list ectx_item) state
                 lang.ML_lang.of_outcome lang.ML_lang.to_outcome
                 lang.ML_lang.of_call lang.ML_lang.is_call
                 nil comp_ectx fill
                 apply_function prim_step.
Proof. split; try easy.
  + apply lang.ML_lang.to_of_outcome.
  + apply lang.ML_lang.of_to_outcome.
  + apply lang.ML_lang.outcome_prim_step.
  + apply lang.ML_lang.call_prim_step.
  + apply lang.ML_lang.prim_step_call_dec.
  + apply lang.ML_lang.prim_step_no_call.
  + apply lang.ML_lang.is_outcome_not_call.
  + apply lang.ML_lang.is_call_in_cont.
  + apply lang.ML_lang.is_call_of_call_inv.
  + intros *. eapply lang.ML_lang.fill_outcome.
  + eapply lang.ML_lang.fill_comp.
  + eapply lang.ML_lang.prim_step_fill.
  + intros *. eapply lang.ML_lang.fill_step_inv.
Qed.

Canonical Structure ML_lang := Language melocoton_lang_mixin_ML.

Record pure_head_step (p : gmap _ _) (e1 e2 : expr) := {
  pure_head_step_safe σ1 : head_reducible p e1 σ1;
  pure_head_step_det σ1 e2' σ2 :
    head_step p e1 σ1 e2' σ2 → σ2 = σ1 ∧ e2' = e2
}.

Lemma pure_head_step_pure_step p e1 e2 :
  pure_head_step p e1 e2 → pure_step p e1 e2.
Proof.
  intros [Hp1 Hp2]. split.
  - intros σ. destruct (Hp1 σ) as (e2' & σ2 & ?).
    eexists e2', σ2. by apply head_prim_step.
  - intros σ1 e2' σ2 ?%head_reducible_prim_step; eauto.
Qed.

Lemma head_prim_reducible p e σ : head_reducible p e σ → reducible p e σ.
Proof. intros (e'&σ'&?). eexists e', σ'. by apply head_prim_step. Qed.
