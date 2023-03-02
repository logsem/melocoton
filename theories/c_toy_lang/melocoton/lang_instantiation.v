From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_toy_lang Require Export lang metatheory.

Local Notation state := (gmap loc heap_cell).

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
  - cbn. destruct a. 2-12:congruence.
    destruct (unmap_val le) eqn:Heq. 2:congruence.
    intros H. injection H. intros <-. cbn. f_equal. now apply IHle.
Qed.

Lemma of_to_cancel e c : to_class e = Some c → of_class c = e.
Proof.
  destruct e; cbn; try congruence.
  - intros H. injection H. intros <-. easy.
  - destruct e. 2-12: congruence. destruct v. destruct l. 1-2: congruence.
    destruct unmap_val eqn:Heq. 2:congruence.
    intros H. injection H. intros <-. cbn. f_equal. now apply unmap_val_map.
Qed.

Lemma fill_class (K : list ectx_item) (e:expr) :
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

Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  induction K in e|-*.
  - intros H; apply H.
  - intros H. cbn in H. specialize (IHK _ H).
    eapply fill_item_val. apply IHK.
Qed.

Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
Proof.
  intros HH. destruct (to_val (fill K e)) eqn:Heq; try done.
  destruct (fill_val K e); try done. congruence.
Qed.

Lemma fill_comp_item k K e : fill (k :: K) e = fill K (fill_item k e).
Proof. reflexivity. Qed.

Lemma fill_tail k K e e' :
  to_val e = None ->
  to_val e' = None ->
  fill_item k e = fill K e' ->
  K = [] ∨ exists K', K = K' ++ [k] /\ e = fill K' e'.
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

Global Instance fill_inj K : Inj (=) (=) (fill K).
Proof.
  intros e1 e2.
  induction K as [|Ki K IH] in e1, e2 |- *; rewrite /Inj; first done.
  rewrite !fill_comp_item. by intros ?%IH%fill_item_inj.
Qed.

Lemma fill_ctx K s vv K' e : 
  fill K' e = fill K (of_class (ExprCall s vv))
  -> (exists v, e = Val v) \/ (exists K2, K = K2 ++ K').
Proof. cbn.
  induction K' as [|[] K' IH] in K,e|-*; intros H; first last.
  1-13: destruct  (IH _ _ H) as [(v & Hv)|(K2 & ->)]; try (cbn in *; congruence).
  1-13:  destruct (to_val e) eqn:Heq; first (apply of_to_val in Heq; by left; eexists).
  1-13:  rewrite fill_comp_item in H.
  1-13:  rewrite fill_app in H; apply fill_inj in H.
  1-13:  apply fill_tail in H as H2; try (cbn; congruence).
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
  @MlanguageMixin expr val function (list ectx_item) state
                 of_class to_class
                 nil (fun a b => b++a) fill
                 apply_function expr_size head_step.
Proof. split.
  + apply to_of_cancel.
  + apply of_to_cancel.
  + intros * HH.
    unshelve epose proof (val_head_stuck p (of_class (ExprVal v)) σ _) as H2.
    { eapply umrel_upclosed; eauto. }
    cbn in *; congruence.
  + intros *. split.
    - inversion 1; simplify_eq. intros []. naive_solver.
    - intros HH. econstructor. naive_solver.
  + done.
  + intros. by rewrite fill_app.
  + apply _.
  + apply fill_class.
  + apply fill_size.
  + intros K K' e s' vv Heq.
    destruct (fill_ctx K' s' vv K e) as [(v&HL)|(K2&HK2)].
    - apply Heq.
    - right. exists v. rewrite HL. easy.
    - left. exists K2. easy.
  + intros p.
    intros K K' e1 e1' σ1 Hfill Hred Hstep; revert K' Hfill.
    induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
    destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
    { rewrite fill_app in Hstep. apply head_ctx_step_val in Hstep.
      apply fill_val in Hstep. exfalso.
      destruct Hstep as [? Hstep]. by destruct e1. }
    rewrite !fill_app /= in Hfill.
    assert (Ki = Ki') as ->.
    { eapply fill_item_no_val_inj, Hfill.
      2: { by eapply val_head_stuck, fill_not_val in Hstep. }
      eapply fill_not_val. by destruct e1. }
    simplify_eq. destruct (IH K') as [K'' ->]; auto.
    exists K''. by rewrite assoc.
  + intros p K e σ1.
    destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
    rewrite fill_app /=.
    intros [v' ?]%head_ctx_step_val%fill_val. right. exists v'.
    destruct e; naive_solver.
  + admit.
Admitted.

Canonical Structure C_lang := Language melocoton_lang_mixin_C.
Canonical Structure C_mlang := lang_to_mlang C_lang.
