From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.language Require Import language.
From melocoton.c_toy_lang Require Export lang metatheory.

Local Notation state := (gmap loc heap_cell).

Lemma map_unmap_val l : unmap_val (map Val l) = Some l.
Proof.
  induction l.
  - easy.
  - cbn. rewrite IHl. easy.
Qed.

Local Lemma to_of_class_C e : to_class_C (of_class_C e) = Some e.
Proof.
  destruct e.
  - easy.
  - cbn. rewrite map_unmap_val. easy.
Qed.

Lemma unmap_val_map le lv : unmap_val le = Some lv → map Val lv = le.
Proof.
  induction le in lv|-*.
  - intros H. injection H. intros <-. easy.
  - cbn. destruct a. 2-12:congruence.
    destruct (unmap_val le) eqn:Heq. 2:congruence.
    intros H. injection H. intros <-. cbn. f_equal. now apply IHle.
Qed.

Local Lemma of_to_class_C e c : to_class_C e = Some c → of_class_C c = e.
Proof.
  destruct e; cbn; try congruence.
  - intros H. injection H. intros <-. easy.
  - destruct e. 2-12: congruence. destruct v. destruct l. 1-2: congruence.
    destruct unmap_val eqn:Heq. 2:congruence.
    intros H. injection H. intros <-. cbn. f_equal. now apply unmap_val_map.
Qed.

Local Lemma fill_class (K : list ectx_item) (e:expr) :
  is_Some (to_class_C (fill K e)) → K = nil ∨ ∃ v, to_class_C e = Some (ExprVal v).
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

Local Notation to_val e :=
  (match to_class_C e with Some (ExprVal v) => Some v | _ => None end).

Local Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  intros. eapply (of_to_class_C e (ExprVal v)).
  repeat case_match; by simplify_eq.
Qed.

Local Lemma to_val_funcall fn vs :
  to_val (FunCall fn vs) = None.
Proof.
  repeat (case_match; simplify_eq; cbn in * ); eauto.
Qed.

Local Hint Resolve to_val_funcall : core.

Local Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  intros [? HH]. case_match; simplify_eq.
  case_match; simplify_eq.
  pose proof (mk_is_Some _ _ H) as H2.
  apply fill_class in H2 as [->|[? ->]]; last done.
  rewrite /= H //.
Qed.

Local Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
Proof.
  intros HH. destruct (to_val (fill K e)) eqn:Heq; try done.
  destruct (fill_val K e); try done. congruence.
Qed.

Local Lemma fill_comp_item k K e : fill (k :: K) e = fill K (fill_item k e).
Proof. reflexivity. Qed.

Local Lemma fill_tail k K e e' :
  to_val e = None →
  to_val e' = None →
  fill_item k e = fill K e' →
  K = [] ∨ ∃ K', K = K' ++ [k] ∧ e = fill K' e'.
Proof.
  intros He He'.
  destruct K.
  + intros _. now left.
  + destruct (@exists_last _ (e0::K)) as (L & l & Hl); first congruence.
    rewrite Hl. unfold fill.
    rewrite foldl_snoc. cbn. intros H. pose proof H as H_copy.
    apply fill_item_no_val_inj in H_copy as ->.
    2: easy.
    2: { destruct (to_val (foldl (flip fill_item) e' L)) eqn:Heq; last done.
         edestruct (fill_val L e'). 1: eexists; apply Heq. congruence. }
    right. eexists. split; first done. now apply fill_item_inj in H.
Qed.

Local Lemma fill_inj K : Inj (=) (=) (fill K).
Proof.
  intros e1 e2.
  induction K as [|Ki K IH] in e1, e2 |- *; rewrite /Inj; first done.
  rewrite !fill_comp_item. by intros ?%IH%fill_item_inj.
Qed.

Local Lemma fill_ctx K s vv K' e :
  fill K' e = fill K (of_class_C (ExprCall s vv)) →
  (∃ v, e = Val v) ∨ (∃ K2, K = K2 ++ K').
Proof. cbn.
  induction K' as [|[] K' IH] in K,e|-*; intros H; first last.
  1-13: destruct  (IH _ _ H) as [(v & Hv)|(K2 & ->)]; try (cbn in *; congruence).
  1-13:  destruct (to_val e) eqn:Heq; first (apply of_to_val in Heq; by left; eexists).
  1-13:  rewrite fill_comp_item in H.
  1-13:  rewrite fill_app in H; apply fill_inj in H.
  1-13:  apply fill_tail in H as H2; try (simplify_eq; eauto; congruence).
  1-13:  destruct H2 as [->|(K3 & -> & HK3)]; try (cbn in *; congruence).
  1-16:  try (right; exists K3; by rewrite <- app_assoc).
  - exfalso. cbn in H. assert (In e (map Val vv)) as Hin.
    + assert (map Val va ++ e :: ve = map Val vv) as <- by congruence.
      apply in_app_iff. right. now left.
    + apply in_map_iff in Hin. destruct Hin as (v & Hv & Hin). rewrite <- Hv in Heq. cbn in Heq. congruence.
  - cbn in H. assert (e = Val (LitV (LitFunPtr s))) as ->; (cbn in *; congruence).
  - cbn. right. eexists. by erewrite app_nil_r.
Qed.

Lemma melocoton_lang_mixin_C :
  @LanguageMixin expr val function (list ectx_item) state
                 of_class_C to_class_C
                 nil comp_ectx fill
                 apply_function head_step.
Proof. split.
  + apply to_of_class_C.
  + apply of_to_class_C.
  + intros *. inversion 1.
  + intros p f vs σ1 e2 σ2. split.
    - intros H. inversion H; subst. inversion H; subst. repeat econstructor; [apply H2|].
      rewrite <- H6. f_equal. eapply map_inj in H1; congruence.
    - intros ([args ee] & H1 & H2 & ->). econstructor; eauto.
  + intros K K' e s' vv Heq.
    destruct (fill_ctx K' s' vv K e) as [(v&HL)|(K2&HK2)].
    - apply Heq.
    - right. exists v. rewrite HL. easy.
    - left. exists K2. easy.
  + intros p1 p2 e1 σ1 e2 σ2 H Hnc.
    inversion H; subst. all: try by econstructor.
    cbn in Hnc. rewrite map_unmap_val in Hnc. congruence.
  + done.
  + intros e; rewrite /comp_ectx app_nil_r //.
  + intros e. easy.
  + intros K1 K2 e. rewrite fill_app //.
  + intros K a b. apply fill_inj.
  + apply fill_class.
  + intros p.
    intros K K' e1 e1' σ1 e2 σ2 Hfill Hred Hstep; revert K' Hfill.
    induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
    destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
    { rewrite fill_app in Hstep. apply head_ctx_step_val in Hstep.
      apply fill_val in Hstep. destruct Hstep as [? Hstep].
      by repeat (case_match; simplify_eq). }
    rewrite !fill_app /= in Hfill.
    assert (Ki = Ki') as ->.
    { eapply fill_item_no_val_inj, Hfill.
      2: { by eapply val_head_stuck, fill_not_val in Hstep. }
      eapply fill_not_val. by destruct e1. }
    simplify_eq. destruct (IH K') as [K'' ->]; auto.
    exists K''. rewrite /comp_ectx assoc //.
  + intros p K e σ1 e2 σ2.
    destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
    rewrite fill_app /=.
    intros [v' ?]%head_ctx_step_val%fill_val. right. exists v'.
    by repeat (case_match; simplify_eq).
Qed.

Canonical Structure C_lang := Language melocoton_lang_mixin_C.


