From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.language Require Import mlanguage.
From melocoton.c_toy_mlang Require Export lang.

Local Notation rel := multirelations.rel.

Definition of_class (e : mixin_expr_class val) : expr := match e with
  ExprVal v => Val v
| ExprCall vf vl => FunCall (Val $ LitV $ LitFunPtr vf) (map Val vl) end.
#[local] Notation omap f x := (match x with Some v => f v | None => None end).
Fixpoint unmap_val el := match el with 
      Val v::er => omap (fun vr => Some (v::vr)) (unmap_val er)
    | nil => Some nil
    | _ => None end.
Definition to_class (e : expr) : option (mixin_expr_class val) := match e with
  Val v => Some (ExprVal v)
| FunCall (Val (LitV (LitFunPtr vf))) el => omap (fun l => Some (ExprCall vf l)) (unmap_val el)
| _ => None end.

Lemma map_unmap_val l : unmap_val (map Val l) = Some l.
Proof.
  induction l.
  - easy.
  - cbn. rewrite IHl. easy.
Qed.

Lemma to_of_cancel e : to_class (of_class e) = Some e.
Proof.
  destruct e.
  - easy.
  - cbn. rewrite map_unmap_val. easy.
Qed.

Lemma unmap_val_map le lv : unmap_val le = Some lv → map Val lv = le.
Proof.
  induction le in lv|-*.
  - intros H. injection H. intros <-. easy.
  - cbn. destruct a. 2-14:congruence.
    destruct (unmap_val le) eqn:Heq. 2:congruence.
    intros H. injection H. intros <-. cbn. f_equal. now apply IHle.
Qed.

Lemma of_to_cancel e c : to_class e = Some c → of_class c = e.
Proof.
  destruct e; cbn; try congruence.
  - intros H. injection H. intros <-. easy.
  - destruct e. 2-14: congruence. destruct v. destruct l. 1-2: congruence.
    destruct unmap_val eqn:Heq. 2:congruence.
    intros H. injection H. intros <-. cbn. f_equal. now apply unmap_val_map.
Qed.

Definition ectx := list ectx_item.

Definition fill (K : ectx) (e : expr) : expr :=
  foldl (flip fill_item) e K.

Definition comp_ectx (K K' : ectx) : ectx :=
  K' ++ K.

Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof. apply foldl_app. Qed.

Lemma fill_class (K : ectx) (e:expr) :
  is_Some (to_class (fill K e)) → K = nil ∨ ∃ v, to_class e = Some (ExprVal v).
Proof.
  intros [v Hv]. revert v Hv. induction K as [|k1 K] using rev_ind; intros v Hv. 1:now left. right.
  rewrite fill_app in Hv.
  destruct k1; cbn in Hv; try congruence.
  + destruct (fill K e) eqn:Heq; cbn in Hv; try congruence. destruct v0. destruct l; cbn in Hv; try congruence.
    revert Hv. edestruct unmap_val eqn:Heq2; try congruence. intros H. injection H. intros <-.
    cbn in IHK. destruct (IHK _ eq_refl) as [->|Hr].
    - cbn in Heq. subst. eexists. cbn. reflexivity.
    - easy.
  + destruct vf. destruct l; cbn in Hv; try congruence. revert Hv. edestruct unmap_val eqn:Heq; try congruence.
    intros H. injection H. intros <-. apply unmap_val_map in Heq.
    assert (In (fill K e) (map Val l)) as [vv [Hvv' Hvv]]%in_map_iff.
    1: rewrite Heq; apply in_app_iff; right; now left.
    destruct (IHK (ExprVal vv)) as [Hl|Hr].
    - rewrite <- Hvv'. easy.
    - subst. cbn in *. subst. eexists. cbn. reflexivity.
    - easy.
Qed.

Lemma val_head_step p v σ φ :
  ¬ rel (head_step p) (Val v, σ) φ.
Proof. inversion 1. Qed.

Lemma call_head_step (p : gmap string function) f vs σ φ :
  rel (head_step p) (of_class (ExprCall f vs), σ) φ ↔
  ∃ (fn : function) (e2 : expr),
    p !! f = Some fn ∧ Some e2 = apply_function fn vs ∧ φ (e2, σ).
Proof.
  split.
  { inversion 1; subst. do 2 eexists. split_and!; eauto. symmetry.
    match goal with H : _ |- _ => apply map_inj in H end; [by subst|].
    congruence. }
  { intros ([? ?] & ? & ? & ? & ?). econstructor; eauto. }
Qed.

Lemma fill_inj K : Inj (=) (=) (fill K).
Proof. induction K as [|Ki K IH]; rewrite /Inj; naive_solver. Qed.

Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  revert e. induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val.
Qed.

Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
Proof. rewrite !eq_None_not_Some. by intros ? ?%fill_val. Qed.

Lemma step_by_val p K' K_redex e1' e1_redex σ φ :
  fill K' e1' = fill K_redex e1_redex →
  match to_class e1' with Some (ExprVal _) => False | _ => True end →
  rel (head_step p) (e1_redex, σ) φ →
  ∃ K'', K_redex = comp_ectx K' K''.
Proof.
  intros Hfill Hred Hstep. revert K_redex Hfill.
  induction K' as [|Ki K IH] using rev_ind=> /= K_redex Hfill; eauto using app_nil_r.
  destruct K_redex as [|Ki' K' _] using @rev_ind; simplify_eq/=.
  { rewrite fill_app in Hstep. apply head_ctx_step_val' in Hstep.
    apply fill_val in Hstep. apply not_eq_None_Some in Hstep.
    destruct e1'; naive_solver. }
  rewrite !fill_app in Hfill.
  assert (Ki = Ki') as ->.
  { eapply fill_item_no_val_inj, Hfill; apply fill_not_val.
    - destruct e1'; naive_solver.
    - eapply val_head_stuck; eauto. }
  simplify_eq. destruct (IH K') as [K'' ->]; auto.
  exists K''. rewrite /comp_ectx -!app_assoc //.
Qed.

Lemma head_ctx_step_val p K e σ1 φ :
  rel (head_step p) (fill K e, σ1) φ →
  K = [] ∨ ∃ v, to_class e = Some (ExprVal v).
Proof.
  destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
  rewrite fill_app /=.
  intros HH%head_ctx_step_val'. apply fill_val in HH. right.
  apply not_eq_None_Some in HH; destruct e; cbn in HH; try congruence.
  eauto.
Qed.

Lemma melocoton_mlang_mixin_C :
  @mlanguage.MlanguageMixin
    expr val function ectx state
    of_class to_class
    nil (fun a b => b++a) fill
    apply_function head_step.
Proof. split.
  + apply to_of_cancel.
  + apply of_to_cancel.
  + apply val_head_step.
  + apply call_head_step.
  + now intros e.
  + intros K1 K2 e. now rewrite fill_app.
  + intros K a b. apply fill_inj.
  + apply fill_class.
  + apply step_by_val.
  + apply head_ctx_step_val.
Qed.

Canonical Structure C_mlang_melocoton := Mlanguage melocoton_mlang_mixin_C.
