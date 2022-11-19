From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.c_toy_lang Require Export lang.


Inductive bogo_head_step (p:program) : expr → state → list unit → expr → state → list expr → Prop :=
  bogo_obs e1 σ1 e2 σ2 :
    head_step p e1 σ1 e2 σ2 →
    bogo_head_step p e1 σ1 [] e2 σ2 [].

Lemma bogo_head_step_elim p e1 σ1 l1 e2 σ2 l2 : 
  bogo_head_step p e1 σ1 l1 e2 σ2 l2 → head_step p e1 σ1 e2 σ2.
Proof. by intros []. Qed.

Lemma bogo_head_step_elim' p e1 σ1 l1 e2 σ2 l2 : 
  bogo_head_step p e1 σ1 l1 e2 σ2 l2 → head_step p e1 σ1 e2 σ2 /\ l1 = [] /\ l2 = [].
Proof. inversion 1;subst. now repeat split. Qed.

Lemma C_lang_mixin p : EctxiLanguageMixin of_val to_val fill_item (bogo_head_step p).
Proof.
  split; apply _ || eauto using bogo_head_step_elim, to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.

(** Language *)
Canonical Structure C_ectxi_lang p := EctxiLanguage (C_lang_mixin p).
Canonical Structure C_ectx_lang p := EctxLanguageOfEctxi (C_ectxi_lang p).
Canonical Structure C_iris_lang p := LanguageOfEctx (C_ectx_lang p).
Coercion C_iris_lang : C_lang.program >-> language.


(** The following lemma is not provable using the axioms of [ectxi_language].
The proof requires a case analysis over context items ([destruct i] on the
last line), which in all cases yields a non-value. To prove this lemma for
[ectxi_language] in general, we would require that a term of the form
[fill_item i e] is never a value. *)
Lemma to_val_fill_some p K e v : to_val (@fill (C_ectxi_lang p) K e) = Some v → K = [] ∧ e = Val v.
Proof.
  intro H. destruct K as [|Ki K]; first by apply of_to_val in H. exfalso.
  assert (to_val e ≠ None) as He.
  { intro A. by rewrite fill_not_val in H. }
  assert (∃ w, e = Val w) as [w ->].
  { destruct e; try done; eauto. }
  assert (to_val (fill (Ki :: K) (Val w)) = None).
  { destruct Ki; simpl; apply fill_not_val; done. }
  by simplify_eq.
Qed.

Lemma prim_step_to_val_is_head_step p e σ1 κs w σ2 efs :
  @prim_step (C_ectxi_lang p) e σ1 κs (Val w) σ2 efs → head_step p e σ1 (Val w) σ2.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some w) as H3; first by rewrite -H2.
  apply to_val_fill_some in H3 as [-> ->]. subst e. eapply bogo_head_step_elim. apply H.
Qed.

(** If [e1] makes a head step to a value under some state [σ1] then any head
 step from [e1] under any other state [σ1'] must necessarily be to a value. *)
Lemma head_step_to_val p e1 σ1 e2 σ2 σ1' e2' σ2' :
  head_step p e1 σ1 e2 σ2 →
  head_step p e1 σ1' e2' σ2' → is_Some (to_val e2) → is_Some (to_val e2').
Proof.
  destruct 1; inversion 1; try naive_solver; congruence.
Qed.
