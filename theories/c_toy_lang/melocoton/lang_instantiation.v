From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_toy_lang Require Export lang metatheory.

Local Notation state := (gmap loc heap_cell).

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

Local Notation to_val e :=
  (match to_class e with Some (ExprVal v) => Some v | _ => None end).

Local Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  intros. eapply (of_to_cancel e (ExprVal v)).
  repeat case_match; by simplify_eq.
Qed.

Local Lemma to_val_funcall fn vs :
  to_val (FunCall fn vs) = None.
Proof.
  repeat (case_match; simplify_eq; cbn in * ); eauto.
Qed.

Local Hint Resolve to_val_funcall : core.

Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  intros [? HH]. case_match; simplify_eq.
  case_match; simplify_eq.
  pose proof (mk_is_Some _ _ H) as H2.
  apply fill_class in H2 as [->|[? ->]]; last done.
  rewrite /= H //.
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

Lemma decompose_expr_val_list ee va ee':
  ee = map Val va ++ ee' →
  (∃ va', ee = map Val va') ∨ (∃ va' ve e', ee = map Val va' ++ e' :: ve ∧ to_val e' = None).
Proof.
  revert va. induction ee' as [| e' ee']; intros * ->.
  { rewrite app_nil_r. left; eauto. }
  destruct e'.
  { specialize (IHee' (va ++ [v])).
    rewrite map_app -app_assoc in IHee'.
    specialize (IHee' eq_refl) as [(va' & HH) | (va' & ve & e' & HH)]; eauto. }
  all: right; eexists va, ee', _; eauto.
Qed.

Lemma not_val_in_vals va va' e' ve:
  to_val e' = None →
  map Val va ≠ map Val va' ++ e' :: ve.
Proof.
  intros HH (l1 & l2 & -> & Heq1 & (? & ? & -> & <- & <-)%map_eq_cons)%map_eq_app.
  done.
Qed.

Lemma head_step_cases p e σ :
    is_Some (to_val e)
  ∨ head_step p (e, σ) (λ _, True)
  ∨ (¬ head_step p (e, σ) (λ _, True) ∧
     ∃ (K : ectx) (e' : expr),
       e = fill K e' ∧
       to_val e' = None ∧
       K ≠ []).
Proof.
  Local Ltac notstuck := right; left; econstructor; eauto.
  Local Ltac stuck := right; right; split; [by inversion 1|eauto].
  Local Ltac inctx Ctxpat := stuck; eexists [Ctxpat], _; split; by eauto.
  Local Ltac isval := left; done.
  Local Tactic Notation "inctx" uconstr(X) := inctx X.
  destruct e.
  - isval.
  - notstuck.
  - destruct e1; try inctx (LetCtx _ _). notstuck.
  - destruct e; try inctx LoadCtx. notstuck.
  - destruct e1; try inctx (StoreLCtx _).
    destruct e2; try inctx (StoreRCtx _). notstuck.
  - destruct e; try inctx MallocCtx. right; left. apply alloc_step.
  - destruct e1; try inctx (FreeLCtx _).
    destruct e2; try inctx (FreeRCtx _). notstuck.
  - destruct e; try inctx (UnOpCtx _). notstuck.
  - destruct e1; try inctx (BinOpLCtx _ _).
    destruct e2; try inctx (BinOpRCtx _ _). notstuck.
  - destruct e1; try inctx (IfCtx _ _). notstuck.
  - notstuck.
  - destruct e; try inctx (FunCallLCtx _).
    pose proof (decompose_expr_val_list _ [] ee eq_refl)
      as [HH|HH]; cbn in HH.
    { destruct HH as (va & ->). right; left. by econstructor. }
    { destruct HH as (va & ve & e' & -> & He'). right; right. split.
      { inversion 1; subst. eapply not_val_in_vals; eauto. }
      exists [FunCallRCtx v va ve], e'. done. }
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
      apply fill_val in Hstep. destruct Hstep as [? Hstep].
      by repeat (case_match; simplify_eq). }
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
    by repeat (case_match; simplify_eq).
  + intros ? ? ?. eapply head_step_cases.
  + econstructor. exact (∅ : gmap _ _).
Qed.

Canonical Structure C_lang := Mlanguage melocoton_lang_mixin_C.
