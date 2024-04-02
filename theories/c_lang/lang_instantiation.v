From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton Require Import stdpp_extra.
From melocoton.language Require Import language.
From melocoton.c_interface Require Import defs.
From melocoton.c_lang Require Export lang metatheory.

Local Notation state := (gmap loc heap_cell).

Lemma melocoton_lang_mixin_C :
  @LanguageMixin expr val function (list ectx_item) state
                 of_val lang.C_lang.to_val lang.C_lang.of_call lang.C_lang.is_call
                 nil comp_ectx fill
                 apply_function prim_step.
Proof. split.
  + apply lang.C_lang.to_of_val.
  + apply lang.C_lang.of_to_val.
  + apply lang.C_lang.val_prim_step.
  + apply lang.C_lang.call_prim_step.
  + apply lang.C_lang.prim_step_call_dec.
  + apply lang.C_lang.prim_step_no_call.
  + apply lang.C_lang.is_val_not_call.
  + apply lang.C_lang.is_call_in_cont.
  + done.
  + done.
  + apply lang.C_lang.is_call_of_call_inv.
  + intros *. eapply lang.C_lang.fill_val.
  + eapply lang.C_lang.fill_comp.
  + done.
  + eapply lang.C_lang.prim_step_fill.
  + intros *. eapply lang.C_lang.fill_step_inv.
Qed.

Canonical Structure C_lang := Language melocoton_lang_mixin_C.

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
