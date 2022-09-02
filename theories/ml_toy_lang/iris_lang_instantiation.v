From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.ml_toy_lang Require Export lang.


(** Language *)
Canonical Structure ml_toy_ectxi_lang p:= EctxiLanguage (ml_toy_lang.ml_toy_lang_mixin p).
Canonical Structure ml_toy_ectx_lang p:= EctxLanguageOfEctxi (ml_toy_ectxi_lang p).
Canonical Structure ml_toy_lang p:= LanguageOfEctx (ml_toy_ectx_lang p).

(* Prefer ml_toy_lang names over ectx_language names. *)
Export ml_toy_lang.

(** The following lemma is not provable using the axioms of [ectxi_language].
The proof requires a case analysis over context items ([destruct i] on the
last line), which in all cases yields a non-value. To prove this lemma for
[ectxi_language] in general, we would require that a term of the form
[fill_item i e] is never a value. *)
Lemma to_val_fill_some (p:ml_program) K e v : to_val (fill K e) = Some v → K = [] ∧ e = Val v.
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

Lemma prim_step_to_val_is_head_step (p:ml_program)e σ1 κs w σ2 efs :
  prim_step e σ1 κs (Val w) σ2 efs → head_step e σ1 κs (Val w) σ2 efs.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some w) as H3; first by rewrite -H2.
  apply to_val_fill_some in H3 as [-> ->]. subst e. done.
Qed.

(** If [e1] makes a head step to a value under some state [σ1] then any head
 step from [e1] under any other state [σ1'] must necessarily be to a value. *)
Lemma head_step_to_val (p:ml_program)e1 σ1 κ e2 σ2 efs σ1' κ' e2' σ2' efs' :
  head_step e1 σ1 κ e2 σ2 efs →
  head_step e1 σ1' κ' e2' σ2' efs' → is_Some (to_val e2) → is_Some (to_val e2').
Proof. destruct 1; inversion 1; naive_solver. Qed.
