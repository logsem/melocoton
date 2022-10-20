From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.ml_toy_lang Require Export iris_lang_instantiation.
From melocoton.ml_toy_lang Require Export metatheory lang.
From melocoton.language Require Import language.
Import ml_toy_lang.

Definition of_class (e : mixin_expr_class val) : expr := match e with
  ExprVal v => Val v
| ExprCall vf vl => Extern vf (map Val vl) end.
#[local] Notation omap f x := (match x with Some v => f v | None => None end).
Fixpoint unmap_val el := match el with 
      Val v::er => omap (fun vr => Some (v::vr)) (unmap_val er)
    | nil => Some nil
    | _ => None end.
Definition to_class (e : expr) : option (mixin_expr_class val) := match e with
  Val v => Some (ExprVal v)
| Extern vf el => omap (fun l => Some (ExprCall vf l)) (unmap_val el)
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
  - cbn. destruct a. 2-17:congruence.
    destruct (unmap_val le) eqn:Heq. 2:congruence.
    intros H. injection H. intros <-. cbn. f_equal. now apply IHle.
Qed.

Lemma of_to_cancel e c : to_class e = Some c → of_class c = e.
Proof.
  destruct e; cbn; try congruence.
  - intros H. injection H. intros <-. easy.
  - destruct unmap_val eqn:Heq. 2:congruence.
    intros H. injection H. intros <-. cbn. f_equal. now apply unmap_val_map.
Qed.

Inductive bogo_head_step' (p:ml_program) : expr → state → expr → state → list expr → Prop :=
  bogo_obs e1 σ1 e2 σ2 t:
    head_step e1 σ1 [] e2 σ2 t →
    bogo_head_step' p e1 σ1 e2 σ2 t.

Lemma bogo_head_step'_elim p e1 σ1 e2 σ2 l2 : 
  bogo_head_step' p e1 σ1 e2 σ2 l2 → head_step e1 σ1 [] e2 σ2 l2.
Proof. by intros []. Qed.

Lemma bogo_head_step'_elim' p e1 σ1 e2 σ2 l2 : 
  bogo_head_step' p e1 σ1 e2 σ2 l2 → head_step e1 σ1 [] e2 σ2 l2 /\ l2 = [].
Proof. inversion 1;subst. split; first done. now inversion H0; congruence. Qed.

Lemma head_step_no_val p v σ1 e2 σ2 efs :
  bogo_head_step' p (Val v) σ1 e2 σ2 efs → False.
Proof.
  intros H. inversion H; subst. inversion H0.
Qed.

Lemma fill_class {p:ml_program} (K : list ectx_item) (e:expr) : 
    is_Some (to_class (ectxi_language.fill K e)) → K = nil ∨ ∃ v, to_class e = Some (ExprVal v).
Proof.
  intros [v Hv]. revert v Hv. induction K as [|k1 K] using rev_ind; intros v Hv. 1:now left. right.
  rewrite fill_app in Hv.
  destruct k1; cbn in Hv; try congruence.
  + revert Hv. edestruct unmap_val eqn:Heq; try congruence.
    intros H. injection H. intros <-. apply unmap_val_map in Heq.
    assert (In (ectxi_language.fill K e) (map Val l)) as [vv [Hvv' Hvv]]%in_map_iff.
    1: rewrite Heq; apply in_app_iff; right; now left.
    destruct (IHK (ExprVal vv)) as [Hl|Hr].
    - rewrite <- Hvv'. easy.
    - subst. cbn in *. subst. eexists. cbn. reflexivity.
    - easy.
Qed.

Inductive split_state : state → state → state → Prop :=
  | MLSplitState σ : split_state σ σ σ.

Definition fill (K : list ectx_item) (e : expr) : expr :=
  @ectxi_language.fill (ml_toy_ectxi_lang (∅ : gmap _ _)) K e.

Lemma melocoton_lang_mixin_C :
  @LanguageMixin expr val ml_function (list ectx_item) state state state
                 of_class to_class
                 nil (fun a b => b++a) fill
                 split_state (λ _ _, True) apply_function bogo_head_step'.
Proof. split.
  + apply to_of_cancel.
  + apply of_to_cancel.
  + apply head_step_no_val.
  + intros p f vs σ1 e2 σ2 efs. split.
    - intros H. inversion H; subst. inversion H0; subst. repeat econstructor; [apply H3|].
      rewrite <- H5. f_equal. eapply map_inj in H2; congruence.
    - intros ([args ee] & H1 & H2 & -> & ->). econstructor. cbn. by eapply ExternS.
  + now intros e.
  + intros K1 K2 e. now rewrite /fill fill_app.
  + intros K a b. apply ectx_language.fill_inj.
  + unfold fill. apply fill_class.
  + intros *. by do 2 (inversion 1).
  + intros *. by do 2 (inversion 1).
  + done.
  + intros ? ? ? _. do 2 eexists. econstructor.
  + done.
  + intros. do 2 eexists. econstructor.
  + intros p. unfold fill.
    change ((@ectxi_language.fill (ml_toy_ectxi_lang (∅:gmap _ _)))) with ((@ectxi_language.fill (ml_toy_ectxi_lang p))).
    intros K' K_redec e1' e1_redex σ1 e2 σ2 efs H Heq [Hstep ->]%bogo_head_step'_elim'.
    destruct (ectx_language.step_by_val K' K_redec e1' e1_redex σ1 nil e2 σ2 nil H) as [K'' HK''].
    1: now destruct e1'; cbn in *.
    1: apply Hstep.
    exists K''. apply HK''.
  + admit.
  + intros p. unfold fill.
    change ((@ectxi_language.fill (ml_toy_ectxi_lang (∅:gmap _ _)))) with ((@ectxi_language.fill (ml_toy_ectxi_lang p))).
    intros K e σ1 e2 σ2 efs (Hstep & ->)%bogo_head_step'_elim'.
    change (gmap string ml_function) with ml_program in p.
    edestruct (ectx_language.head_ctx_step_val K e σ1 nil e2 σ2 nil) as [Hl|Hr].
    1: apply Hstep.
    1: right; destruct Hl as (v&Hv); exists v; destruct e; cbn in *; congruence.
    1: left; now rewrite Hr.
Admitted.

Canonical Structure C_lang_melocoton := Language melocoton_lang_mixin_C.
