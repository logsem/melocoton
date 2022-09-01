From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.language Require Import language.

Section Linking.
  Context {val : Type}.
  Context {state : Type}.
  Context (Λ1 Λ2 : language val state).

  Definition func : Type :=
    (Λ1.(func) + Λ2.(func)).

  Inductive simple_expr : Type :=
  (* The linked module produces a value
     (following one of the underlying modules producing a value) *)
  | LinkExprV (v : val)
  (* The linked module performs a call (corresponding to an external call
     performed by one of the underlying modules). This is not necessarily an
     external call of the linked module, it can correspond to a function
     implemented in the other linked module. *)
  | LinkExprCall (fn_name : string) (args : list val)
  (* Incoming call of one of the functions implemented by the linked module. It
     will be dispatched against the corresponding underlying module. *)
  | LinkRunFunction (fn : func) (args : list val)
  (* Execution of code belonging to the first underlying module. *)
  | LinkExpr1 (e : Λ1.(language.expr))
  (* Execution of code belonging to the second underlying module. *)
  | LinkExpr2 (e : Λ2.(language.expr)).

  Definition ectx : Type :=
    list (Λ1.(ectx) + Λ2.(ectx)).

  Definition expr : Type :=
    simple_expr * ectx.

  Definition of_class (c : mixin_expr_class val) : expr :=
    match c with
    | ExprVal v => (LinkExprV v, [])
    | ExprCall fn args => (LinkExprCall fn args, [])
    end.

  Definition to_class (e : expr) : option (mixin_expr_class val) :=
    match e with
    | (LinkExprV v, []) => Some (ExprVal v)
    | (LinkExprCall fn_name args, []) => Some (ExprCall fn_name args)
    | _ => None
    end.

  Definition empty_ectx : ectx := [].

  Definition comp_ectx (K1 K2 : ectx) : ectx :=
    K2 ++ K1.

  Definition fill (K : ectx) (e : expr) : expr :=
    let '(se, k) := e in
    (se, k ++ K).

  Definition apply_func (fn : func) (args : list val) : option expr :=
    Some (LinkRunFunction fn args, []).

  Local Notation prog := (gmap string func).

  Definition proj1_prog (P : prog) : language.prog Λ1 :=
    omap (λ fn, match fn with inl fn1 => Some fn1 | inr _ => None end) P.
  Definition proj2_prog (P : prog) : language.prog Λ2 :=
    omap (λ fn, match fn with inl _ => None | inr fn2 => Some fn2 end) P.

  Inductive head_step (P : prog) : expr → state → expr → state → list expr → Prop :=
  (* Internal step of an underlying module. *)
  (* XXX the final [] means that we reason about sequential programs. this could
     probably be unforced simply by changing the language interface to only
     describe sequential operational semantics by removing threads. *)
  | Step1S e1 e1' σ σ' :
    prim_step (proj1_prog P) e1 σ e1' σ' [] →
    head_step P (LinkExpr1 e1, []) σ (LinkExpr1 e1', []) σ []
  | Step2S e2 e2' σ σ' :
    prim_step (proj2_prog P) e2 σ e2' σ' [] →
    head_step P (LinkExpr2 e2, []) σ (LinkExpr2 e2', []) σ []
  (* Entering a function *)
  | RunFunction1S σ fn1 args e1 :
    language.apply_func fn1 args = Some e1 →
    head_step P (LinkRunFunction (inl fn1) args, []) σ (LinkExpr1 e1, []) σ []
  | RunFunction2S σ fn2 args e2 :
    language.apply_func fn2 args = Some e2 →
    head_step P (LinkRunFunction (inr fn2) args, []) σ (LinkExpr2 e2, []) σ []
  (* Producing a value when execution is finished *)
  | Val1S e1 v σ :
    to_val e1 = Some v →
    head_step P (LinkExpr1 e1, []) σ (LinkExprV v, []) σ []
  | Val2S e2 v σ :
    to_val e2 = Some v →
    head_step P (LinkExpr2 e2, []) σ (LinkExprV v, []) σ []
  (* Continuing execution by returning a value to its caller *)
  | Ret1S v k1 σ :
    head_step P (LinkExprV v, [inl k1]) σ
                (LinkExpr1 (language.fill k1 (of_val Λ1 v)), []) σ []
  | Ret2S v k2 σ :
    head_step P (LinkExprV v, [inr k2]) σ
                (LinkExpr2 (language.fill k2 (of_val Λ2 v)), []) σ []
  (* Stuck module calls bubble up as calls at the level of the linking module.
     (They may get unstuck then, if they match a function implemented by the
     other module.) *)
  | MakeCall1S k1 e1 fn_name args σ :
    language.to_class e1 = Some (ExprCall fn_name args) →
    proj1_prog P !! fn_name = None →
    head_step P (LinkExpr1 (language.fill k1 e1), []) σ
                (LinkExprCall fn_name args, [inl k1]) σ []
  | MakeCall2S k2 e2 fn_name args σ :
    language.to_class e2 = Some (ExprCall fn_name args) →
    proj2_prog P !! fn_name = None →
    head_step P (LinkExpr2 (language.fill k2 e2), []) σ
                (LinkExprCall fn_name args, [inr k2]) σ []
  (* Resolve an internal call to a module function *)
  | CallS fn_name fn args σ :
    P !! fn_name = Some fn →
    head_step P (LinkExprCall fn_name args, []) σ
                (LinkRunFunction fn args, []) σ [].

  Lemma language_mixin :
    LanguageMixin (val:=val) of_class to_class empty_ectx comp_ectx fill
      apply_func head_step.
  Proof using.
    constructor.
    - intros c. destruct c; reflexivity.
    - intros e c. destruct e as [e k]. destruct e; cbn.
      1,2: destruct k. all: inversion 1; cbn; auto.
    - intros p v σ e σ' efs. cbn. inversion 1.
    - intros p fn_name v σ e σ' efs. split.
      + cbn. inversion 1; subst; naive_solver.
      + intros [fn (? & Hfn & -> & ->)]. cbn.
        unfold apply_func in Hfn; simplify_eq; by constructor.
    - intros [e k]. rewrite /fill /empty_ectx app_nil_r //.
    - intros K1 K2 [e k]. rewrite /fill /comp_ectx app_assoc //.
    - intros K [e1 k1] [e2 k2]. cbn. inversion 1; subst.
      rewrite (app_inv_tail K k1 k2) //.
    - intros K [e k]. unfold fill. intros Hsome.
      destruct (decide (K = empty_ectx)). by left. exfalso.
      assert (k ++ K ≠ []). { intros [? ?]%app_eq_nil. done. }
      cbn in Hsome. destruct (k ++ K) eqn:?.
      2: destruct e; by inversion Hsome. by destruct e.
    - intros p K' K_redex [e1' k1'] [e1_redex k1_redex] σ1 [e2 k2] σ2 efs.
      rewrite /fill. intros [-> Hk]%pair_equal_spec.
      destruct e1_redex; destruct k1' as [|u1' k1']; cbn; try by inversion 1.
      all: intros _; inversion 1; subst; unfold comp_ectx; cbn; eauto.
      all: naive_solver.
    - intros p K [e k] σ1 [e2 k2] σ2 efs. rewrite /fill. inversion 1; subst.
      all: try match goal with H : _ |- _ => symmetry in H; apply app_nil in H end.
      all: try match goal with H : _ |- _ => symmetry in H; apply app_singleton in H end.
      all: naive_solver.
  Qed.

  Canonical Structure link_lang (Λ1 Λ2 : language val state) : language val state :=
    Language language_mixin.

End Linking.
