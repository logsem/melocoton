From stdpp Require Import relations strings gmap.
From iris.algebra Require Import ofe.
From iris.prelude Require Import options.
From melocoton Require Export multirelations commons.

Section mlanguage_mixin.
  Context {expr val func ectx state : Type}.
  Notation mixin_expr_class := (@mixin_expr_class val).

  Context (of_class : mixin_expr_class → expr).
  Context (to_class : expr → option mixin_expr_class).

  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).

  (** A program is a map from function names to function bodies. *)
  Local Notation mixin_prog := (gmap string func).

  Context (apply_func : func → list val → option expr).
  Context (expr_size : expr → nat).
  Context (head_step : mixin_prog → umrel (expr * state)).

  Notation is_head_redex p x := (head_step p x (λ _, True)).
  Notation to_val e := (match to_class e with Some (ExprVal v) => Some v | _ => None end).

  Record MlanguageMixin := {
    (** Expression classification *)
    mixin_to_of_class c : to_class (of_class c) = Some c;
    mixin_of_to_class e c : to_class e = Some c → of_class c = e;

    (** Reduction behavior of the special classes of expressions *)
    (** mixin_val_head_step is not an iff because the backward direction is trivial *)
    mixin_val_head_step p v σ X :
      head_step p (of_class (ExprVal v), σ) X → False;
    mixin_call_head_step p f vs σ X :
      head_step p (of_class (ExprCall f vs), σ) X ↔
      (∀ (fn : func) (e2 : expr),
        p !! f = Some fn → Some e2 = apply_func fn vs → X (e2, σ));

    (** Evaluation contexts *)
    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    (* The the things in a class contain only values in redex positions (or the
       redex is the topmost one). *)
    mixin_fill_class K e :
      is_Some (to_class (fill K e)) → K = empty_ectx ∨ ∃ v, to_class e = Some (ExprVal v);
    mixin_fill_size K e :
      K ≠ empty_ectx → expr_size e < expr_size (fill K e);
    mixin_call_in_ctx K K' e f vs :
      fill K e = fill K' (of_class (ExprCall f vs)) →
      (∃ K'', K' = comp_ectx K K'') ∨ (∃ v, of_class (ExprVal v) = e);

    (** Given a head redex [e1_redex] somewhere in a term, and another
        decomposition of the same term into [fill K' e1'] such that [e1'] is not
        a value, then the head redex context is [e1']'s context [K'] filled with
        another context [K''].  In particular, this implies [e1 = fill K''
        e1_redex] by [fill_inj], i.e., [e1]' contains the head redex.)

        This implies there can be only one head redex, see
        [head_redex_unique]. *)
    mixin_step_by_val p K' K_redex e1' e1_redex σ :
      fill K' e1' = fill K_redex e1_redex →
      match to_class e1' with Some (ExprVal _) => False | _ => True end →
      is_head_redex p (e1_redex, σ) →
      ∃ K'', K_redex = comp_ectx K' K'';

    (** If [fill K e] takes a head step, then either [e] is a value or [K] is
        the empty evaluation context. In other words, if [e] is not a value
        wrapping it in a context does not add new head redex positions. *)
    mixin_head_ctx_step_val p K e σ :
      is_head_redex p (fill K e, σ) → K = empty_ectx ∨ ∃ v, to_class e = Some (ExprVal v);

    (** If e is not head_reducible, we can recurse into it to find a head_redex in a context.
        Since context are strictly decreasing, this implies there is no NB (except for values) *)
    mixin_head_redex_cases p e σ : 
      is_Some (to_val e)
    ∨ is_head_redex p (e, σ)
    ∨ (¬ is_head_redex p (e, σ) ∧
        (∃ K e', e = fill K e' ∧ to_val e' = None ∧ K ≠ empty_ectx))
  }.
End mlanguage_mixin.

Arguments mixin_expr_class : clear implicits.
Global Notation mixin_prog func := (gmap string func).

Structure mlanguage {val : Type} := Mlanguage {
  expr : Type;
  func : Type;
  ectx : Type;
  state : Type;

  of_class : mixin_expr_class val → expr;
  to_class : expr → option (mixin_expr_class val);
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  apply_func : func → list val → option expr;
  expr_size : expr → nat;
  head_step : mixin_prog func → umrel (expr * state);

  mlanguage_mixin :
    MlanguageMixin (val:=val) of_class to_class empty_ectx comp_ectx fill
      apply_func expr_size head_step
}.

Declare Scope expr_scope.
Bind Scope expr_scope with expr.

Arguments mlanguage : clear implicits.
Arguments Mlanguage {_ expr _ _ _ _ _ _ _ _ apply_func _ head_step}.
Arguments of_class {_} _ _.
Arguments to_class {_ _} _.
Arguments empty_ectx {_ _}.
Arguments comp_ectx {_ _} _ _.
Arguments fill {_ _} _ _.
Arguments apply_func {_ _}.
Arguments expr_size {_ _} _.
Arguments head_step {_ _} _.

Definition expr_class {val} (Λ : mlanguage val) := mixin_expr_class val.
(* A [Definition] throws off Coq's "old" ("tactic") unification engine *)
Notation prog Λ := (mixin_prog Λ.(func)).

Definition to_val {val} {Λ : mlanguage val} (e : expr Λ) :=
  match to_class e with
  | Some (ExprVal v) => Some v
  | _ => None
  end.
Definition of_val {val} (Λ : mlanguage val) (v : val) := of_class Λ (ExprVal v).

Definition to_call {val} {Λ : mlanguage val} (e : expr Λ) :=
  match to_class e with
  | Some (ExprCall f v) => Some (f, v)
  | _ => None
  end.
Definition of_call {val} (Λ : mlanguage val) f (v : list val) := of_class Λ (ExprCall f v).

Definition is_head_redex {val} {Λ : mlanguage val} (p : prog Λ) x := head_step p x (λ _, True).

(* From an ectx_language, we can construct a mlanguage. *)
Section mlanguage.
  Context {val : Type}.
  Context {public_state : Type}.
  Context {Λ : mlanguage val}.
  Implicit Types v : val.
  Implicit Types vs : list val.
  Implicit Types e : expr Λ.
  Implicit Types c : expr_class Λ.
  Implicit Types K : ectx Λ.
  Implicit Types p : prog Λ.
  Implicit Types X : expr Λ * state Λ → Prop.

  Lemma to_of_class c : to_class (of_class Λ c) = Some c.
  Proof. apply mlanguage_mixin. Qed.
  Lemma of_to_class e c : to_class e = Some c → of_class Λ c = e.
  Proof. apply mlanguage_mixin. Qed.

  Lemma of_class_inj k1 k2 : of_class Λ k1 = of_class Λ k2 → k1 = k2.
  Proof.
    intros H. enough (Some k1 = Some k2) by congruence.
    rewrite <- !to_of_class. rewrite H. done.
  Qed.

  Lemma to_val_of_call f vs : to_val (of_call Λ f vs) = None.
  Proof. rewrite /to_val /of_call to_of_class. done. Qed.
  Lemma to_call_of_val v : to_call (of_val Λ v) = None.
  Proof. rewrite /to_call /of_val to_of_class. done. Qed.
  Lemma is_val_is_class e : is_Some (to_val e) → is_Some (to_class e).
  Proof. rewrite /to_val /is_Some. destruct (to_class e) as [[|]|]; naive_solver. Qed.
  Lemma is_call_is_class e : is_Some (to_call e) → is_Some (to_class e).
  Proof. rewrite /to_call /is_Some. destruct (to_class e) as [[|]|]; naive_solver. Qed.

  Lemma val_head_step p v σ X :
    head_step p (of_class Λ (ExprVal v), σ) X → False.
  Proof. apply mlanguage_mixin. Qed.
  Lemma call_head_step p f vs σ X :
    head_step p (of_class Λ (ExprCall f vs), σ) X ↔
    (∀ fn e2, p !! f = Some fn → Some e2 = apply_func fn vs → X (e2, σ)).
  Proof. apply mlanguage_mixin. Qed.

  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply mlanguage_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply mlanguage_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply mlanguage_mixin. Qed.
  Lemma fill_class' K e :
    is_Some (to_class (fill K e)) → K = empty_ectx ∨ ∃ v, to_class e = Some (ExprVal v).
  Proof. apply mlanguage_mixin. Qed.
  Lemma fill_size K e :
      K ≠ empty_ectx → expr_size e < expr_size (fill K e).
  Proof. apply mlanguage_mixin. Qed.
  Lemma step_by_val' p K' K_redex e1' e1_redex σ :
      fill K' e1' = fill K_redex e1_redex →
      match to_class e1' with Some (ExprVal _) => False | _ => True end →
      is_head_redex p (e1_redex, σ) →
      ∃ K'', K_redex = comp_ectx K' K''.
  Proof. apply mlanguage_mixin. Qed.
  Lemma head_ctx_step_val' p K e σ :
    is_head_redex p (fill K e, σ) → K = empty_ectx ∨ ∃ v, to_class e = Some (ExprVal v).
  Proof. apply mlanguage_mixin. Qed.
  Lemma call_in_ctx K K' e f vs :
    fill K e = fill K' (of_class Λ (ExprCall f vs)) →
    (∃ K'', K' = comp_ectx K K'') ∨ (∃ v, of_class Λ (ExprVal v) = e).
  Proof. apply mlanguage_mixin. Qed.
  Lemma call_in_ctx_to_val K K' e f vs :
    fill K e = fill K' (of_class _ (ExprCall f vs)) →
    (∃ K'', K' = comp_ectx K K'') ∨ is_Some (to_val e).
  Proof.
    intros [H1|(x&Hx)]%call_in_ctx; auto.
    right. exists x. rewrite /to_val -Hx to_of_class//.
  Qed.
  Lemma head_redex_cases p e σ :
      is_Some (to_val e)
    ∨ is_head_redex p (e, σ)
    ∨ (¬ is_head_redex p (e, σ) ∧
        (∃ K e', e = fill K e' ∧ to_val e' = None ∧ K ≠ empty_ectx)).
  Proof. apply mlanguage_mixin. Qed.
  Lemma fill_class K e :
    is_Some (to_class (fill K e)) → K = empty_ectx ∨ is_Some (to_val e).
  Proof.
    intros [?|[v Hv]]%fill_class'; first by left. right.
    rewrite /to_val Hv. eauto.
  Qed.
  Lemma to_val_fill_call K f vs :
    to_val (fill K (of_call Λ f vs)) = None.
  Proof.
    destruct (to_val (fill K (of_call Λ f vs))) eqn:HH; eauto.
    destruct (fill_class K (of_call Λ f vs)) as [H1|H2].
    { unfold to_val in HH. repeat case_match; simplify_eq. eauto. }
    { subst. rewrite fill_empty in HH. unfold to_val in HH.
      repeat case_match; simplify_eq.
      unfold of_call in *. by rewrite -> to_of_class in *. }
    { clear HH. rewrite -> to_val_of_call in H2. by apply is_Some_None in H2. }
  Qed.
  Lemma call_call_in_ctx K K' fn fn' vs vs' :
    fill K (of_class _ (ExprCall fn vs)) = fill K' (of_class _ (ExprCall fn' vs')) →
    K' = comp_ectx K empty_ectx ∧ fn' = fn ∧ vs' = vs.
  Proof.
    intros HH. destruct (call_in_ctx _ _ _ _ _ HH) as [[K'' ->]|[? H2]].
    { rewrite -fill_comp in HH. apply fill_inj in HH.
      destruct (fill_class K'' (of_class _ (ExprCall fn' vs'))) as [Hc|Hc].
      { rewrite -HH /= to_of_class //. }
      2: { exfalso. rewrite /to_val to_of_class in Hc. by apply is_Some_None in Hc. }
      subst K''. rewrite fill_empty in HH. apply of_class_inj in HH. by simplify_eq. }
    { exfalso. apply of_class_inj in H2. congruence. }
  Qed.
  Lemma step_by_val p K' K_redex e1' e1_redex σ :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      is_head_redex p (e1_redex, σ) →
      ∃ K'', K_redex = comp_ectx K' K''.
  Proof.
    rewrite /to_val => ? He1'. eapply step_by_val'; first done.
    destruct (to_class e1') as [[]|]; done.
  Qed.
  Lemma head_ctx_step_val p K e σ:
    is_head_redex p (fill K e, σ) → K = empty_ectx ∨ is_Some (to_val e).
  Proof.
    intros [?|[v Hv]]%head_ctx_step_val'; first by left. right.
    rewrite /to_val Hv. eauto.
  Qed.
  Lemma call_head_step_inv p f vs σ X :
    head_step p (of_class Λ (ExprCall f vs), σ) X →
    (∀ fn e2, p !! f = Some fn → Some e2 = apply_func fn vs → X (e2, σ)).
  Proof. eapply call_head_step. Qed.
  Lemma call_head_step_intro p f vs fn σ er :
    p !! f = Some fn →
    Some er = apply_func fn vs →
    head_step p (of_call Λ f vs, σ) (λ '(e', σ'), e' = er ∧ σ' = σ).
  Proof.
    intros ? ?. eapply call_head_step; intros; simplify_eq.
    split; congruence.
  Qed.

  Lemma head_step_is_head_redex p x X : head_step p x X → is_head_redex p x.
  Proof.
    intros H. eapply umrel_upclosed; eauto.
  Qed.

  (* All non-value redexes are at the root.  In other words, all sub-redexes are
     values. *)
  Definition sub_redexes_are_values (e : expr Λ) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Definition prim_step_mrel (p : prog Λ) : multirelation (expr Λ * state Λ) :=
    λ '(e1, σ1) X,
      ∃ K e1',
        e1 = fill K e1' ∧
        head_step p (e1', σ1) (λ '(e2', σ2), X (fill K e2', σ2)).

  Program Definition prim_step (p : prog Λ) : umrel (expr Λ * state Λ) :=
    {| mrel := prim_step_mrel p |}.
  Next Obligation.
    intros p [e1 σ1] *.
    intros (K & e' & -> & Hstep) HH. do 2 eexists. split_and!; eauto.
    eapply umrel_upclosed; eauto. intros [? ?]. eauto.
  Qed.

  Definition has_ub (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∃ X, prim_step p (e, σ) X ∧ ∀ x, ¬ X x.

  (** * Some lemmas about this language *)
  Lemma to_of_val v : to_val (of_val Λ v) = Some v.
  Proof. rewrite /to_val /of_val to_of_class //. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val Λ v = e.
  Proof.
    rewrite /to_val /of_val => Hval. apply of_to_class.
    destruct (to_class e) as [[]|]; simplify_option_eq; done.
  Qed.
  Lemma of_to_val_flip v e : of_val Λ v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.
  Lemma val_head_stuck p e σ X: head_step p (e, σ) X → to_val e = None.
  Proof.
    destruct (to_val e) as [v|] eqn:Hval; last done.
    rewrite -(of_to_val e v) //. intros []%val_head_step.
  Qed.
  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof.
    intros Hval. destruct (fill_class K e) as [HK|He].
    - apply is_val_is_class. done.
    - subst K. move: Hval. rewrite fill_empty. done.
    - done.
  Qed.
  Lemma val_stuck p e σ X: prim_step p (e, σ) X → to_val e = None.
  Proof.
    intros (K & e1' & -> & ?%val_head_stuck).
    apply eq_None_not_Some. by intros ?%fill_val%eq_None_not_Some.
  Qed.

  Lemma to_of_call f vs : to_call (of_call Λ f vs) = Some (f, vs).
  Proof. rewrite /to_call /of_call to_of_class //. Qed.
  Lemma of_to_call e f vs : to_call e = Some (f, vs) → of_call Λ f vs = e.
  Proof.
    rewrite /to_call /of_call => Hval. apply of_to_class.
    destruct (to_class e) as [[] | ]; simplify_option_eq; done.
  Qed.
  Lemma of_to_call_flip f vs e : of_call Λ f vs = e → to_call e = Some (f, vs).
  Proof. intros <-. apply to_of_call. Qed.

  Global Instance of_val_inj : Inj (=) (=) (of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Lemma extcall_ctx_has_ub p K f vs σ :
    p !! f = None →
    has_ub p (fill K (of_class Λ (ExprCall f vs))) σ.
  Proof.
    intros H.
    exists (fun x => False).
    split; last tauto.
    econstructor. eexists; split; first done.
    eapply call_head_step. intros ?? Hc _. rewrite H in Hc; congruence.
  Qed.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma head_prim_step p e1 σ1 X :
    head_step p (e1, σ1) X → prim_step p (e1, σ1) X.
  Proof.
    intros Hstep. exists empty_ectx, e1. split.
    - by rewrite fill_empty.
    - intros *. eapply umrel_upclosed; eauto.
      intros [? ?]. rewrite fill_empty //.
  Qed.

  Lemma fill_prim_step p K e1 σ1 X X' :
    (∀ e2 σ2, X (e2, σ2) → X' (fill K e2, σ2)) →
    prim_step p (e1, σ1) X →
    prim_step p (fill K e1, σ1) X'.
  Proof.
    intros HX (K' & e1' & -> & Hstep). rewrite fill_comp /=.
    do 2 eexists. split_and!; eauto.
    eapply umrel_upclosed; eauto. intros [? ?].
    rewrite -fill_comp. eauto.
  Qed.
  Lemma fill_prim_step' p K e1 σ1 X :
    prim_step p (e1, σ1) X →
    prim_step p (fill K e1, σ1)
        (λ '(e2', σ2), ∃ e2, e2' = fill K e2 ∧ X (e2, σ2)).
  Proof.
    intros Hstep. eapply fill_prim_step with (X' := λ _, _) in Hstep.
    - eapply Hstep.
    - intros ? ? ?. simpl. eexists. eauto.
  Qed.

  Lemma prim_head_step p e σ X :
    prim_step p (e, σ) X → sub_redexes_are_values e → head_step p (e, σ) X.
  Proof.
    intros (K & e1' & -> & Hstep) ?.
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty. eapply umrel_upclosed; [apply Hstep|].
    intros [? ?]. rewrite fill_empty //.
  Qed.

  Lemma head_reducible_prim_step_ctx p K e1 σ1 X :
    is_head_redex p (e1, σ1) →
    prim_step p (fill K e1, σ1) X →
    head_step p (e1, σ1) (λ '(e2', σ2), ∀ e2, e2 = fill K e2' → X (e2, σ2)).
  Proof.
    intros HhstepK (K' & e1' & HKe1 & Hstep).
    edestruct (step_by_val p K) as [K'' ?];
      eauto using val_head_stuck; simplify_eq/=; first by eapply head_step_is_head_redex.
    rewrite -fill_comp in HKe1; simplify_eq.
    apply head_ctx_step_val in HhstepK as [?|[v ?]]; simplify_eq.
    - rewrite fill_empty. eapply umrel_upclosed; [apply Hstep|].
      intros [e σ]. rewrite -fill_comp fill_empty //. by intros ? ? ->.
    - apply val_head_stuck in Hstep; simplify_eq.
  Qed.

  Lemma head_reducible_prim_step p e1 σ1 X :
    is_head_redex p (e1, σ1) →
    prim_step p (e1, σ1) X →
    head_step p (e1, σ1) X.
  Proof.
    intros Hred Hpstep.
    epose proof (head_reducible_prim_step_ctx _ empty_ectx _ _ X Hred) as Hhstep.
    eapply umrel_upclosed.
    - eapply Hhstep. by rewrite fill_empty.
    - intros [e σ]. rewrite fill_empty. eauto.
  Qed.

  Lemma prim_step_call_inv p K f vs e' σ X :
    prim_step p (fill K (of_call Λ f vs), σ) X →
    ∀ er fn,
      Some er = apply_func fn vs → p !! f = Some fn →
      X (fill K er, σ).
  Proof.
    intros (K' & e1 & Hctx & Hstep) ?? Heq1 Heq2.
    pose proof (head_step_is_head_redex _ _ _ Hstep) as Hredex.
    eapply step_by_val in Hredex as H'; eauto; last apply to_val_of_call.
    destruct H' as [K'' Hctx']; subst K'.
    rewrite -fill_comp in Hctx. eapply fill_inj in Hctx.
    destruct (fill_class K'' e1) as [->|Hval].
    - apply is_call_is_class. erewrite of_to_call_flip; eauto.
    - rewrite fill_empty in Hctx. subst e1.
      eapply call_head_step_inv in Hstep. 2-3:done.
      rewrite -fill_comp fill_empty// in Hstep.
    - apply val_head_stuck in Hstep. apply not_eq_None_Some in Hval. done.
  Qed.

  Lemma val_prim_step p v σ X :
   ¬ prim_step p (of_val Λ v, σ) X.
  Proof.
    intros (K & e1' & Heq & Hstep').
    edestruct (fill_val K e1') as (v1''& ?).
    { rewrite -Heq. rewrite to_of_val. by exists v. }
    eapply val_head_step.
    erewrite <-(of_to_val e1') in Hstep'; eauto.
  Qed. 

  Lemma fill_step_inv p K e1' σ1 X :
    to_val e1' = None →
    prim_step p (fill K e1', σ1) X →
    prim_step p (e1', σ1) (λ '(e2', σ2), X (fill K e2', σ2)).
  Proof.
    intros ? (K'' & e'' & Heq & Hstep).
    pose proof (head_step_is_head_redex _ _ _ Hstep) as Hredex.
    eapply step_by_val in Hredex as Hstep'; eauto. destruct Hstep' as [K' ->].
    rewrite -fill_comp in Heq. apply (inj (fill _)) in Heq as ->.
    do 2 eexists; split_and!; eauto. clear Hredex.
    eapply multirelations.umrel_upclosed; eauto. intros [? ?].
    rewrite -fill_comp//.
  Qed.

  Lemma call_prim_step_fill p K f vs σ X :
    prim_step p (fill K (of_class Λ (ExprCall f vs)), σ) X →
    ∀ (fn : func Λ) e2,
      p !! f = Some fn →
      apply_func fn vs = Some e2 →
      X (fill K e2, σ).
  Proof.
    intros (K' & e1 & Hfill%eq_sym & Hstep) ?? HH1 HH2.
    pose proof (call_in_ctx _ _ _ _ _ Hfill) as [[K'' ->]|[? Hval]].
    { rewrite -fill_comp in Hfill. apply fill_inj in Hfill. subst e1.
      pose proof (head_step_is_head_redex _ _ _ Hstep) as Hredex.
      pose proof (head_ctx_step_val _ _ _ _ Hredex) as [->|[? Hval]].
      { rewrite fill_empty in Hstep. eapply call_head_step in Hstep. 2-3:done.
        rewrite -!fill_comp fill_empty//. }
      { exfalso. rewrite /to_val to_of_class// in Hval. } }
    { exfalso. subst. apply val_head_stuck in Hstep. rewrite /to_val to_of_class// in Hstep. }
  Qed.

  Lemma call_prim_step p f vs σ X :
    prim_step p (of_class Λ (ExprCall f vs), σ) X →
    ∀ (fn : func Λ) e2,
      p !! f = Some fn →
      apply_func fn vs = Some e2 →
      X (e2, σ).
  Proof.
    intros H. epose proof (call_prim_step_fill p empty_ectx _ _ _ _) as Hp.
    rewrite !fill_empty in Hp. intros fn e2 H1 H2. specialize (Hp H fn e2 H1).
    rewrite fill_empty// in Hp. by eapply Hp.
  Qed.

  (* There is no NB *)
  Lemma prim_step_is_total p e σ : to_val e = None → prim_step p (e,σ) (λ _, True).
  Proof.
    intros H.
    induction e using (induction_ltof1 _ (expr_size)); unfold ltof in *.
    destruct (head_redex_cases p e σ) as [(v&Hv)|[Hredex|(Hnredex&K&e'&->&He'&HK)]].
    - congruence.
    - eapply head_prim_step, Hredex.
    - eapply fill_prim_step; last first; first eapply H0.
      + by eapply fill_size.
      + done.
      + tauto.
  Qed.

  Class IntoVal (e : expr Λ) (v : val) :=
    into_val : of_val Λ v = e.

  Class AsVal (e : expr Λ) := as_val : ∃ v, of_val Λ v = e.
  (* There is no instance [IntoVal → AsVal] as often one can solve [AsVal] more
  efficiently since no witness has to be computed. *)
  Global Instance as_vals_of_val vs : TCForall AsVal (of_val Λ <$> vs).
  Proof.
    apply TCForall_Forall, Forall_fmap, Forall_true=> v.
    rewrite /AsVal /=; eauto.
  Qed.

  Record pure_step p (e1 : expr Λ) (e2 : expr Λ) := {
    pure_step_not_val : to_val e1 = None;
    pure_step_det σ1 X :
      prim_step p (e1, σ1) X → X (e2, σ1)
  }.

  Class PureExec (φ : Prop) (n : nat) p (e1 : expr Λ) (e2 : expr Λ) :=
    pure_exec : φ → relations.nsteps (pure_step p) n e1 e2.

  Lemma pure_exec_fill φ n p e1 e2 K :
    PureExec φ n p e1 e2 →
    PureExec φ n p (fill K e1) (fill K e2).
  Proof.
    intros H Hφ. specialize (H Hφ). induction H as [|n x y z [Hval Hdet] Hstep IH]; econstructor.
    - econstructor.
      + by eapply fill_not_val.
      + intros σ1 X HH%fill_step_inv; last apply Hval.
        apply Hdet in HH; eauto.
    - apply IH.
  Qed.

  Lemma pure_step_ctx p K e1 e2 :
    pure_step p e1 e2 →
    pure_step p (fill K e1) (fill K e2).
  Proof.
    intros [Hred Hstep]. split.
    - by eapply fill_not_val.
    - intros σ1 X HstepK%fill_step_inv; last done.
      apply Hstep in HstepK. eauto.
  Qed.

  Lemma pure_step_nsteps_ctx K n p e1 e2 :
    relations.nsteps (pure_step p) n e1 e2 →
    relations.nsteps (pure_step p) n (fill K e1) (fill K e2).
  Proof. eauto using nsteps_congruence, pure_step_ctx. Qed.

  Lemma pure_exec_ctx K P n p e1 e2 :
    PureExec P n p e1 e2 →
    PureExec P n p (fill K e1) (fill K e2).
  Proof. rewrite /PureExec; eauto using pure_step_nsteps_ctx. Qed.

End mlanguage.

(* discrete OFE instance for expr *)
Definition exprO {val} {Λ : mlanguage val} := leibnizO (expr Λ).
Global Instance expr_equiv {val} {Λ : mlanguage val} : Equiv (expr Λ). apply exprO. Defined.
