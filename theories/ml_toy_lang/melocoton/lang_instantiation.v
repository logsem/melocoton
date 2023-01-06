From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.interop Require Import lang_to_mlang.
From melocoton.ml_toy_lang Require Import iris.lang_instantiation.
From melocoton.language Require Import language.
From melocoton.ml_toy_lang Require Export lang metatheory.

Import ML_lang.

Local Notation state := (gmap loc (option (list val))).

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
  - cbn. destruct a. 2-18:congruence.
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

Definition fill (K : list ectx_item) (e : expr) : expr :=
  @ectxi_language.fill (ml_toy_ectxi_lang (∅ : gmap _ _)) K e.

Lemma fill_comp k K e : fill (k::K) e = fill K (fill_item k e).
Proof.
  reflexivity.
Qed.

Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  induction K in e|-*.
  - intros H; apply H.
  - intros H. cbn in H. specialize (IHK _ H).
    eapply fill_item_val. apply IHK.
Qed.

Lemma fill_tail k K e e' : to_val e = None -> to_val e' = None -> fill_item k e = fill K e' -> K = [] ∨ exists K', K = K' ++ [k] /\ e = fill K' e'.
Proof. intros He He'.
  destruct K.
  + intros _. now left.
  + destruct (@exists_last _ (e0::K)) as (L & l & Hl); first congruence.
    rewrite Hl. unfold fill, ectxi_language.fill.
    rewrite foldl_snoc. cbn. intros H. pose proof H as H_copy.
    apply fill_item_no_val_inj in H_copy as ->.
    2: easy. 
    2: { destruct (to_val (foldl (flip fill_item) e' L)) eqn:Heq; last done.
         edestruct (fill_val L e'). 1: eexists; apply Heq. congruence. }
    right. eexists. split; first done. now apply fill_item_inj in H.
Qed.

Lemma fill_ctx K s vv K' e : 
  fill K' e = fill K (of_class (ExprCall s vv))
  -> (exists v, e = Val v) \/ (exists K2, K = K2 ++ K').
Proof. cbn.
  induction K' as [|[] K' IH] in K,e|-*; intros H; first last.
  1-22: destruct  (IH _ _ H) as [(v & Hv)|(K2 & ->)]; try (cbn in *; congruence).
  1-22:  destruct (to_val e) eqn:Heq; first (apply of_to_val in Heq; by left; eexists).
  1-22:  rewrite fill_comp in H.
  1-22:  unfold fill in H; rewrite fill_app in H; apply ectx_language.fill_inj in H.
  1-22:  apply fill_tail in H as H2; try (cbn; congruence).
  1-22:  destruct H2 as [->|(K3 & -> & HK3)]; try (cbn in *; congruence).
  1-24:  try (right; exists K3; by rewrite <- app_assoc).
  - exfalso. cbn in H. assert (In e (map Val vv)) as Hin.
    + assert (map Val va ++ e :: ve = map Val vv) as <- by congruence.
      apply in_app_iff. right. now left.
    + apply in_map_iff in Hin. destruct Hin as (v & Hv & Hin). rewrite <- Hv in Heq. cbn in Heq. congruence.
  - cbn. right. eexists. by erewrite app_nil_r.
Qed.

Lemma melocoton_lang_mixin_ML :
  @LanguageMixin expr val ml_function (list ectx_item) state
                 of_class to_class
                 nil (fun a b => b++a) fill
                 apply_function bogo_head_step'.
Proof. split.
  + apply to_of_cancel.
  + apply of_to_cancel.
  + apply head_step_no_val.
  + intros p f vs σ1 e2 σ2 efs. split.
    - intros H. inversion H; subst. inversion H0; subst. repeat econstructor; [apply H3|].
      rewrite <- H5. f_equal. eapply map_inj in H2; congruence.
    - intros ([args ee] & H1 & H2 & -> & ->). econstructor. cbn. by eapply ExternS.
  + intros K K' e s' vv Heq.
    destruct (fill_ctx K' s' vv K e) as [(v&HL)|(K2&HK2)].
    - apply Heq.
    - right. exists v. rewrite HL. easy.
    - left. exists K2. easy.
  + intros p1 p2 e1 σ1 e2 σ2 efs H Hnc. inversion H; subst. econstructor. inversion H0; subst. all: try by econstructor.
    cbn in Hnc. rewrite map_unmap_val in Hnc. congruence.
  + now intros e.
  + intros K1 K2 e. now rewrite /fill fill_app.
  + intros K a b. apply ectx_language.fill_inj.
  + unfold fill. apply fill_class.
  + intros p. unfold fill.
    change ((@ectxi_language.fill (ml_toy_ectxi_lang (∅:gmap _ _)))) with ((@ectxi_language.fill (ml_toy_ectxi_lang p))).
    intros K' K_redec e1' e1_redex σ1 e2 σ2 efs H Heq [Hstep ->]%bogo_head_step'_elim'.
    destruct (ectx_language.step_by_val K' K_redec e1' e1_redex σ1 nil e2 σ2 nil H) as [K'' HK''].
    1: now destruct e1'; cbn in *.
    1: apply Hstep.
    exists K''. apply HK''.
  + intros p. unfold fill.
    change ((@ectxi_language.fill (ml_toy_ectxi_lang (∅:gmap _ _)))) with ((@ectxi_language.fill (ml_toy_ectxi_lang p))).
    intros K e σ1 e2 σ2 efs (Hstep & ->)%bogo_head_step'_elim'.
    change (gmap string ml_function) with ml_program in p.
    edestruct (ectx_language.head_ctx_step_val K e σ1 nil e2 σ2 nil) as [Hl|Hr].
    1: apply Hstep.
    1: right; destruct Hl as (v&Hv); exists v; destruct e; cbn in *; congruence.
    1: left; now rewrite Hr.
Qed.

Canonical Structure ML_lang := Language melocoton_lang_mixin_ML.
(* Canonical Structure ML_mlang := lang_to_mlang ML_lang. *)
