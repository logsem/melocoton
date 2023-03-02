From stdpp Require Import relations strings gmap.
From iris.algebra Require Import ofe.
From iris.prelude Require Import options.
From melocoton Require Export commons.

Section language_mixin.
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
  Context (head_step : mixin_prog → expr → state → expr → state → Prop).

  Record LanguageMixin := {
    (** Expression classification *)
    mixin_to_of_class c : to_class (of_class c) = Some c;
    mixin_of_to_class e c : to_class e = Some c → of_class c = e;

    (** Reduction behavior of the special classes of expressions *)
    (** mixin_val_head_step is not an iff because the backward direction is trivial *)
    mixin_val_head_step p v σ1 e2 σ2 :
      head_step p (of_class (ExprVal v)) σ1 e2 σ2 → False;
    mixin_call_head_step p f vs σ1 e2 σ2 :
      head_step p (of_class (ExprCall f vs)) σ1 e2 σ2 ↔
      ∃ (fn : func),
        p !! f = Some fn ∧ Some e2 = apply_func fn vs ∧ σ2 = σ1;
    mixin_call_in_ctx K K' e s' vv :
      fill K e = fill K' (of_class (ExprCall s' vv))
      → (∃ K'', K' = comp_ectx K K'') ∨ (∃ v, of_class (ExprVal v) = e);

    mixin_head_step_mp_call p1 p2 e1 σ1 e2 σ2 :
      head_step p1 e1 σ1 e2 σ2 → to_class e1 = None → head_step p2 e1 σ1 e2 σ2;

    (** Evaluation contexts *)
    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    (* The the things in a class contain only values in redex positions (or the
       redex is the topmost one). *)
    mixin_fill_class K e :
      is_Some (to_class (fill K e)) → K = empty_ectx ∨ ∃ v, to_class e = Some (ExprVal v);

    (** Given a head redex [e1_redex] somewhere in a term, and another
        decomposition of the same term into [fill K' e1'] such that [e1'] is not
        a value, then the head redex context is [e1']'s context [K'] filled with
        another context [K''].  In particular, this implies [e1 = fill K''
        e1_redex] by [fill_inj], i.e., [e1]' contains the head redex.)

        This implies there can be only one head redex, see
        [head_redex_unique]. *)
    mixin_step_by_val p K' K_redex e1' e1_redex σ1 e2 σ2 :
      fill K' e1' = fill K_redex e1_redex →
      match to_class e1' with Some (ExprVal _) => False | _ => True end →
      head_step p e1_redex σ1 e2 σ2 →
      ∃ K'', K_redex = comp_ectx K' K'';

    (** If [fill K e] takes a head step, then either [e] is a value or [K] is
        the empty evaluation context. In other words, if [e] is not a value
        wrapping it in a context does not add new head redex positions. *)
    (* FIXME: This is the exact same conclusion as [mixin_fill_class]... is
       there some pattern or reduncancy here? *)
    mixin_head_ctx_step_val p K e σ1 e2 σ2 :
      head_step p (fill K e) σ1 e2 σ2 → K = empty_ectx ∨ ∃ v, to_class e = Some (ExprVal v);
  }.
End language_mixin.

Arguments mixin_expr_class : clear implicits.
Global Notation mixin_prog func := (gmap string func).

Structure language {val : Type} := Language {
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
  head_step : mixin_prog func → expr → state → expr → state → Prop;

  language_mixin :
    LanguageMixin (val:=val) of_class to_class empty_ectx comp_ectx fill
      apply_func head_step
}.

Declare Scope expr_scope.
Bind Scope expr_scope with expr.

Arguments language : clear implicits.
Arguments Language {_ expr _ _ _ _ _ _ _ _ apply_func head_step}.
Arguments of_class {_} _ _.
Arguments to_class {_ _} _.
Arguments empty_ectx {_ _}.
Arguments comp_ectx {_ _} _ _.
Arguments fill {_ _} _ _.
Arguments apply_func {_ _}.
Arguments head_step {_ _} _ _ _ _ _.

Definition expr_class {val} (Λ : language val) := mixin_expr_class val.
(* A [Definition] throws off Coq's "old" ("tactic") unification engine *)
Notation prog Λ := (mixin_prog Λ.(func)).

Definition to_val {val} {Λ : language val} (e : expr Λ) :=
  match to_class e with
  | Some (ExprVal v) => Some v
  | _ => None
  end.
Definition of_val {val} (Λ : language val) (v : val) := of_class Λ (ExprVal v).

Definition to_call {val} {Λ : language val} (e : expr Λ) :=
  match to_class e with
  | Some (ExprCall f v) => Some (f, v)
  | _ => None
  end.
Definition of_call {val} (Λ : language val) f (v : list val) := of_class Λ (ExprCall f v).

(* From an ectx_language, we can construct a language. *)
Section language.
  Context {val : Type}.
  Context {Λ : language val}.
  Implicit Types v : val.
  Implicit Types vs : list val.
  Implicit Types e : expr Λ.
  Implicit Types c : expr_class Λ.
  Implicit Types K : ectx Λ.
  Implicit Types p : prog Λ.

  Lemma to_of_class c : to_class (of_class Λ c) = Some c.
  Proof. apply language_mixin. Qed.
  Lemma of_to_class e c : to_class e = Some c → of_class Λ c = e.
  Proof. apply language_mixin. Qed.

  Lemma of_class_inj k1 k2 : of_class Λ k1 = of_class Λ k2 -> k1 = k2.
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

  Lemma val_head_step p v σ1 e2 σ2 :
    head_step p (of_class Λ (ExprVal v)) σ1 e2 σ2 → False.
  Proof. apply language_mixin. Qed.
  Lemma call_head_step p f vs σ1 e2 σ2 :
    head_step p (of_class Λ (ExprCall f vs)) σ1 e2 σ2 ↔
    ∃ fn, p !! f = Some fn ∧ Some e2 = apply_func fn vs ∧ σ2 = σ1.
  Proof. apply language_mixin. Qed.

  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply language_mixin. Qed.
  Lemma fill_class' K e :
    is_Some (to_class (fill K e)) → K = empty_ectx ∨ ∃ v, to_class e = Some (ExprVal v).
  Proof. apply language_mixin. Qed.
  Lemma step_by_val' p K' K_redex e1' e1_redex σ1 e2 σ2 :
      fill K' e1' = fill K_redex e1_redex →
      match to_class e1' with Some (ExprVal _) => False | _ => True end →
      head_step p e1_redex σ1 e2 σ2 →
      ∃ K'', K_redex = comp_ectx K' K''.
  Proof. apply language_mixin. Qed.
  Lemma head_ctx_step_val' p K e σ1 e2 σ2 :
    head_step p (fill K e) σ1 e2 σ2 → K = empty_ectx ∨ ∃ v, to_class e = Some (ExprVal v).
  Proof. apply language_mixin. Qed.
  Lemma call_in_ctx K K' e s' vv : 
      fill K e = fill K' (of_class _ (ExprCall s' vv))
      → (∃ K'', K' = comp_ectx K K'') ∨ (∃ v, of_class _ (ExprVal v) = e).
  Proof. apply language_mixin. Qed.
  Lemma call_in_ctx_to_val K K' e s' vv : 
      fill K e = fill K' (of_class _ (ExprCall s' vv))
      → (∃ K'', K' = comp_ectx K K'') ∨ is_Some (to_val e).
  Proof.
    intros [H1|(x&Hx)]%call_in_ctx.
    - by left.
    - right. exists x. unfold to_val. rewrite <- Hx. now rewrite to_of_class.
  Qed.
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

  Lemma head_step_no_call p1 p2 e1 σ1 e2 σ2 :
      head_step p1 e1 σ1 e2 σ2 → to_class e1 = None → head_step p2 e1 σ1 e2 σ2.
  Proof.
    apply language_mixin.
  Qed.

  Lemma step_by_val p K' K_redex e1' e1_redex σ1 e2 σ2 :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      head_step p e1_redex σ1 e2 σ2 →
      ∃ K'', K_redex = comp_ectx K' K''.
  Proof.
    rewrite /to_val => ? He1'. eapply step_by_val'; first done.
    destruct (to_class e1') as [[]|]; done.
  Qed.
  Lemma head_ctx_step_val p K e σ1 e2 σ2 :
    head_step p (fill K e) σ1 e2 σ2 → K = empty_ectx ∨ is_Some (to_val e).
  Proof.
    intros [?|[v Hv]]%head_ctx_step_val'; first by left. right.
    rewrite /to_val Hv. eauto.
  Qed.
  Lemma call_head_step_inv p f vs σ1 e2 σ2 :
    head_step p (of_class Λ (ExprCall f vs)) σ1 e2 σ2 →
    ∃ fn, p !! f = Some fn ∧ Some e2 = apply_func fn vs ∧ σ2 = σ1.
  Proof. eapply call_head_step. Qed.
  Lemma call_head_step_intro p f vs fn σ1 er :
    p !! f = Some fn →
    Some er = apply_func fn vs →
    head_step p (of_call Λ f vs) σ1 er σ1.
  Proof. intros ? ?. eapply call_head_step; eexists; eauto. Qed.

  Definition head_reducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ', head_step p e σ e' σ'.
  Definition head_irreducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∀ e' σ', ¬head_step p e σ e' σ'.
  Definition head_stuck (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ head_irreducible p e σ.

  (* All non-value redexes are at the root.  In other words, all sub-redexes are
     values. *)
  Definition sub_redexes_are_values (e : expr Λ) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Inductive prim_step (p : prog Λ) : expr Λ → state Λ → expr Λ → state Λ → Prop :=
    Prim_step K e1 e2 σ1 σ2 e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step p e1' σ1 e2' σ2 → prim_step p e1 σ1 e2 σ2.

  Lemma Prim_step' p K e1 σ1 e2 σ2 :
    head_step p e1 σ1 e2 σ2 → prim_step p (fill K e1) σ1 (fill K e2) σ2.
  Proof. econstructor; eauto. Qed.

  Definition reducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ', prim_step p e σ e' σ'.
  Definition irreducible (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    ∀ e' σ', ¬prim_step p e σ e' σ'.
  Definition stuck (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ irreducible p e σ.
  Definition not_stuck (p : prog Λ) (e : expr Λ) (σ : state Λ) :=
    is_Some (to_val e) ∨ reducible p e σ.

  (** * Some lemmas about this language *)
  Lemma prim_step_inv p e1 e2 σ1 σ2 :
    prim_step p e1 σ1 e2 σ2 →
    ∃ K e1' e2', e1 = fill K e1' ∧ e2 = fill K e2' ∧ head_step p e1' σ1 e2' σ2.
  Proof. inversion 1; subst; do 3 eexists; eauto. Qed.
  Lemma to_of_val v : to_val (of_val Λ v) = Some v.
  Proof. rewrite /to_val /of_val to_of_class //. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val Λ v = e.
  Proof.
    rewrite /to_val /of_val => Hval. apply of_to_class.
    destruct (to_class e) as [[]|]; simplify_option_eq; done.
  Qed.
  Lemma of_to_val_flip v e : of_val Λ v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.
  Lemma val_head_stuck p e σ e' σ' : head_step p e σ e' σ' → to_val e = None.
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
  Lemma val_stuck p e σ e' σ' : prim_step p e σ e' σ' → to_val e = None.
  Proof.
    intros (?&?&? & -> & -> & ?%val_head_stuck)%prim_step_inv.
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

  Lemma not_reducible p e σ : ¬reducible p e σ ↔ irreducible p e σ.
  Proof. unfold reducible, irreducible. naive_solver. Qed.
  Lemma reducible_not_val p e σ : reducible p e σ → to_val e = None.
  Proof. intros (?&?&?); eauto using val_stuck. Qed.
  Lemma val_irreducible p e σ : is_Some (to_val e) → irreducible p e σ.
  Proof. intros [??] ?? ?%val_stuck. by destruct (to_val e). Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val _ Λ). 
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.
  Lemma not_not_stuck p e σ : ¬not_stuck p e σ ↔ stuck p e σ.
  Proof.
    rewrite /stuck /not_stuck -not_eq_None_Some -not_reducible.
    destruct (decide (to_val e = None)); naive_solver.
  Qed.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma not_head_reducible p e σ : ¬head_reducible p e σ ↔ head_irreducible p e σ.
  Proof. unfold head_reducible, head_irreducible. naive_solver. Qed.

  (** The decomposition into head redex and context is unique.

      In all sensible instances, [comp_ectx K' empty_ectx] will be the same as
      [K'], so the conclusion is [K = K' ∧ e = e'], but we do not require a law
      to actually prove that so we cannot use that fact here. *)
  Lemma head_redex_unique p K K' e e' σ :
    fill K e = fill K' e' →
    head_reducible p e σ →
    head_reducible p e' σ →
    K = comp_ectx K' empty_ectx ∧ e = e'.
  Proof.
    intros Heq (e2 & σ2 & Hred) (e2' & σ2' & Hred').
    edestruct (step_by_val p K' K e' e) as [K'' HK];
      [by eauto using val_head_stuck..|].
    subst K. move: Heq. rewrite -fill_comp. intros <-%(inj (fill _)).
    destruct (head_ctx_step_val _ _ _ _ _ _ Hred') as [HK''|[]%not_eq_None_Some].
    - subst K''. rewrite fill_empty. done.
    - by eapply val_head_stuck.
  Qed.

  Lemma head_prim_step p e1 σ1 e2 σ2 :
    head_step p e1 σ1 e2 σ2 → prim_step p e1 σ1 e2 σ2.
  Proof. apply Prim_step with empty_ectx; by rewrite ?fill_empty. Qed.

  Lemma head_step_not_stuck p e σ e' σ' :
    head_step p e σ e' σ' → not_stuck p e σ.
  Proof. rewrite /not_stuck /reducible /=. eauto 10 using head_prim_step. Qed.

  Lemma fill_prim_step p K e1 σ1 e2 σ2 :
    prim_step p e1 σ1 e2 σ2 → prim_step p (fill K e1) σ1 (fill K e2) σ2.
  Proof.
    intros (K' & e1' & e2' & -> & -> & ?) % prim_step_inv.
    rewrite !fill_comp. by econstructor.
  Qed.
  Lemma fill_reducible p K e σ : reducible p e σ → reducible p (fill K e) σ.
  Proof.
    intros (e'&σ'&?). exists (fill K e'), σ'. by apply fill_prim_step.
  Qed.
  Lemma head_prim_reducible p e σ : head_reducible p e σ → reducible p e σ.
  Proof. intros (e'&σ'&?). eexists e', σ'. by apply head_prim_step. Qed.
  Lemma head_prim_fill_reducible p e K σ :
    head_reducible p e σ → reducible p (fill K e) σ.
  Proof. intro. by apply fill_reducible, head_prim_reducible. Qed.
  Lemma head_prim_irreducible p e σ : irreducible p e σ → head_irreducible p e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.

  Lemma prim_head_step p e σ e' σ' :
    prim_step p e σ e' σ' → sub_redexes_are_values e → head_step p e σ e' σ'.
  Proof.
    intros Hprim ?. destruct (prim_step_inv _ _ _ _ _ Hprim) as (K & e1' & e2' & -> & -> & Hstep).
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite !fill_empty /head_reducible; eauto.
  Qed.
  Lemma prim_head_reducible p e σ :
    reducible p e σ → sub_redexes_are_values e → head_reducible p e σ.
  Proof. intros (e'&σ'&Hprim) ?. do 2 eexists; by eapply prim_head_step. Qed.
  Lemma prim_head_irreducible p e σ :
    head_irreducible p e σ → sub_redexes_are_values e → irreducible p e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
  Qed.

  Lemma head_stuck_stuck p e σ :
    head_stuck p e σ → sub_redexes_are_values e → stuck p e σ.
  Proof.
    intros [] ?. split; first done. by apply prim_head_irreducible.
  Qed.

  Lemma head_reducible_prim_step_ctx p K e1 σ1 e2 σ2 :
    head_reducible p e1 σ1 →
    prim_step p (fill K e1) σ1 e2 σ2 →
    ∃ e2', e2 = fill K e2' ∧ head_step p e1 σ1 e2' σ2.
  Proof.
    intros (e2''&σ2''&HhstepK) (K' & e1' & e2' & HKe1 & -> & Hstep) % prim_step_inv.
    edestruct (step_by_val p K) as [K'' ?];
      eauto using val_head_stuck; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp; split; first done.
    apply head_ctx_step_val in HhstepK as [?|[v ?]]; simplify_eq.
    - by rewrite !fill_empty.
    - apply val_head_stuck in Hstep; simplify_eq.
  Qed.

  Lemma head_reducible_prim_step p e1 σ1 e2 σ2 :
    head_reducible p e1 σ1 →
    prim_step p e1 σ1 e2 σ2 →
    head_step p e1 σ1 e2 σ2.
  Proof.
    intros.
    edestruct (head_reducible_prim_step_ctx p empty_ectx) as (?&?&?);
      rewrite ?fill_empty; eauto.
    by simplify_eq; rewrite fill_empty.
  Qed.


  Lemma reducible_mono p1 p2 e σ : p1 ⊆ p2 → reducible p1 e σ → reducible p2 e σ.
  Proof.
    intros Hsub (e2 & σ2 & (K & e1' & e2' & -> & -> & H)%prim_step_inv).
    exists (fill K e2'), σ2. econstructor; first done. 1:done.
    destruct (to_class e1') as [[]|] eqn:Heq.
    - exfalso. eapply val_head_step. apply of_to_class in Heq. erewrite Heq. done.
    - apply of_to_class in Heq. subst e1'. apply call_head_step in H.
      destruct H as (Fn & HFn & Happly & ->).
      apply call_head_step. exists Fn. repeat split; try done.
      eapply lookup_weaken; done. 
    - eapply head_step_no_call; done. 
  Qed.

  Lemma fill_stuck (P : prog Λ) e σ K : stuck P e σ → stuck P (fill K e) σ.
  Proof.
    intros Hstuck; split.
    + apply fill_not_val, Hstuck.
    + intros e'' σ'' (K_redex &e1 &e2 &Heq &-> &Hhead)%prim_step_inv.
      edestruct (step_by_val P K K_redex _ _ _ _ _ Heq ltac:(apply Hstuck) Hhead) as (K'' & ->).
      rewrite -fill_comp in Heq. apply fill_inj in Heq as ->.
      eapply (proj2 Hstuck). econstructor; eauto.
  Qed.

  Lemma fill_not_stuck (P : prog Λ) e σ K : not_stuck P (fill K e) σ → not_stuck P e σ.
  Proof.
    intros [Hval | Hred].
    - left. by eapply fill_val.
    - destruct Hred as (e' & σ' & (K_redex &e1 &e2 &Heq &-> &Hhead)%prim_step_inv).
      destruct (decide (to_val e = None)) as [Hnval | Hval]; first last.
      { left. destruct (to_val e) as [v | ]; by eauto. }
      edestruct (step_by_val P K K_redex _ _ _ _ _ Heq Hnval Hhead) as (K'' & ->).
      rewrite -fill_comp in Heq. apply fill_inj in Heq as ->.
      right. eexists _, _. econstructor; eauto.
  Qed.

  Lemma prim_step_call_inv p K f vs e' σ σ' :
    prim_step p (fill K (of_call Λ f vs)) σ e' σ' →
    ∃ er fn, Some er = apply_func fn vs ∧ p !! f = Some fn ∧ e' = fill K er ∧ σ' = σ.
  Proof.
    intros (K' & e1 & e2 & Hctx & -> & Hstep)%prim_step_inv.
    eapply step_by_val in Hstep as H'; eauto; last apply to_val_of_call.
    destruct H' as [K'' Hctx']; subst K'.
    rewrite -fill_comp in Hctx. eapply fill_inj in Hctx.
    destruct (fill_class K'' e1) as [->|Hval].
    - apply is_call_is_class. erewrite of_to_call_flip; eauto.
    - rewrite fill_empty in Hctx. subst e1. exists e2.
      apply call_head_step_inv in Hstep as (fn & ? & -> & ->).
      exists fn. rewrite -fill_comp fill_empty. naive_solver.
    - unfold is_Some in Hval. erewrite val_head_stuck in Hval; naive_solver.
  Qed.

  Lemma val_prim_step p v σ e' σ' :
   ¬ prim_step p (of_val Λ v) σ e' σ'.
  Proof.
    intros (K & e1' & e2' & Heq & -> & Hstep') % prim_step_inv.
    edestruct (fill_val K e1') as (v1''& ?).
    { rewrite -Heq. rewrite to_of_val. by exists v. }
    eapply val_head_step.
    erewrite <-(of_to_val e1') in Hstep'; eauto.
  Qed.

  Lemma fill_reducible_prim_step p e e' σ σ' K :
    reducible p e σ → prim_step p (fill K e) σ e' σ' → ∃ e'', e' = fill K e'' ∧ prim_step p e σ e'' σ'.
  Proof.
    intros (e1 & σ1 & (K'' & e1'' & e2'' & ->  & -> & Hhead) % prim_step_inv) Hprim.
    rewrite fill_comp in Hprim.
    eapply head_reducible_prim_step_ctx in Hprim as (e1' & -> & Hhead'); last by rewrite /head_reducible; eauto.
    eexists. rewrite -fill_comp; by eauto using Prim_step'.
  Qed.

  Lemma reducible_fill p e σ K : reducible p e σ → reducible p (fill K e) σ.
  Proof.
    intros (e' & σ' & Hs). inversion Hs; subst.
    eexists (fill (comp_ectx K K0) e2'), σ'.
    econstructor; rewrite ?fill_comp //.
  Qed.

  Lemma reducible_call_is_in_prog p e K σ s vv :
    reducible p (fill K e) σ →
    to_call e = Some (s,vv) →
    p !! s <> None.
  Proof.
    intros [e' [σ' Hred]] H2. unfold to_call in H2. destruct to_class as [[]|] eqn:Heq; try congruence.
    apply of_to_class in Heq as Heq2; subst. injection H2; intros -> ->.
    apply prim_step_call_inv in Hred.
    destruct Hred as (er & fn & Her & Hfn & _).
    rewrite Hfn; congruence.
  Qed.

  Lemma fill_step_inv K p e1' σ1 e2 σ2 :
    to_val e1' = None → prim_step p (fill K e1') σ1 e2 σ2 →
    ∃ e2', e2 = fill K e2' ∧ prim_step p e1' σ1 e2' σ2.
  Proof.
    intros H1. inversion 1; simplify_eq.
    destruct (step_by_val _ _ _ _ _ _ _ _ H0 H1 H3) as (K'' & ->).
    rewrite <- fill_comp in *.
    apply fill_inj in H0; simplify_eq. eexists. split; eauto.
    by econstructor.
  Qed.

  Lemma fill_inv p K e σ : to_val e = None → reducible p (fill K e) σ → reducible p e σ.
  Proof.
    intros H1 (e'&σ'&(e2'&->&H2)%fill_step_inv). 2:easy.
    exists e2',σ'. easy.
  Qed.

  Lemma head_call_pure p f vs σ e2 σ' σ2 :
    head_step p (of_class Λ (ExprCall f vs)) σ e2 σ' →
    head_step p (of_class Λ (ExprCall f vs)) σ2 e2 σ2.
  Proof.
    intros (fn & H1 & H2 & H3)%call_head_step. apply call_head_step.
    exists fn. repeat split; easy.
  Qed.

End language.

(* discrete OFE instance for expr and thread_id *)
Definition exprO {val} {Λ : language val} := leibnizO (expr Λ).
Global Instance expr_equiv {val} {Λ : language val} : Equiv (expr Λ). apply exprO. Defined.

