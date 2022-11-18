From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.

Class linkable {val} (Λ : mlanguage val) (public_state : Type) := Linkable {
  private_state : Type;
  split_state : Λ.(state) → public_state → private_state → Prop;
  split_state_inj σ σ' pubσ privσ :
    split_state σ pubσ privσ →
    split_state σ' pubσ privσ →
    σ = σ';
}.

Ltac simplify_split_state :=
  repeat match goal with
  | H1 : split_state _ ?x ?y,
    H2 : split_state _ ?x ?y |- _ =>
      pose proof (split_state_inj _ _ x y H2 H1) as ->
  end.

Module Link.
Section Linking.
  Context {val : Type}.
  Context (public_state : Type).
  Context (Λ1 Λ2 : mlanguage val).
  Context {lk1: linkable Λ1 public_state}.
  Context {lk2: linkable Λ2 public_state}.

  Definition func : Type :=
    (Λ1.(func) + Λ2.(func)).

  Inductive simple_expr : Type :=
  (* The linked module produces a value
     (following one of the underlying modules producing a value) *)
  | ExprV (v : val)
  (* The linked module performs a call (corresponding to an external call
     performed by one of the underlying modules). This is not necessarily an
     external call of the linked module, it can correspond to a function
     implemented in the other linked module. *)
  | ExprCall (fn_name : string) (args : list val)
  (* Incoming call of one of the functions implemented by the linked module. It
     will be dispatched against the corresponding underlying module. *)
  | RunFunction (fn : func) (args : list val)
  (* Execution of code belonging to the first underlying module. *)
  | Expr1 (e : Λ1.(mlanguage.expr))
  (* Execution of code belonging to the second underlying module. *)
  | Expr2 (e : Λ2.(mlanguage.expr)).

  Definition ectx : Type :=
    list (Λ1.(ectx) + Λ2.(ectx)).

  (* expr need to be wrapped in a fresh inductive for the language canonical
     structure to work when using WP *)
  Inductive expr : Type :=
    LkE (se: simple_expr) (k: ectx).

  Definition private_state : Type :=
    (lk1.(private_state) * lk2.(private_state)).
  Notation LkSE se := (LkE se []).

  Inductive state : Type :=
    | St (pubσ : public_state)
             (privσ1 : lk1.(linking.private_state))
             (privσ2 : lk2.(linking.private_state))
    | St1 (σ1 : Λ1.(mlanguage.state)) (privσ2 : lk2.(linking.private_state))
    | St2 (privσ1 : lk1.(linking.private_state)) (σ2 : Λ2.(mlanguage.state)).

  Inductive split_state : state → public_state → private_state → Prop :=
    | LinkSplitSt pubσ privσ1 privσ2 :
      split_state (St pubσ privσ1 privσ2) pubσ (privσ1, privσ2).

  Definition of_class (c : mixin_expr_class val) : expr :=
    match c with
    | ExprVal v => LkSE (ExprV v)
    | commons.ExprCall fn args => LkSE (ExprCall fn args)
    end.

  Definition to_class (e : expr) : option (mixin_expr_class val) :=
    match e with
    | LkSE (ExprV v) => Some (ExprVal v)
    | LkSE (ExprCall fn_name args) => Some (commons.ExprCall fn_name args)
    | _ => None
    end.

  Definition empty_ectx : ectx := [].

  Definition comp_ectx (K1 K2 : ectx) : ectx :=
    K2 ++ K1.

  Definition fill (K : ectx) (e : expr) : expr :=
    let 'LkE se k := e in
    LkE se (k ++ K).

  Definition apply_func (fn : func) (args : list val) : option expr :=
    Some (LkSE (RunFunction fn args)).

  Local Notation prog := (gmap string func).

  Definition proj1_prog (p : prog) : mlanguage.prog Λ1 :=
    omap (λ fn, match fn with inl fn1 => Some fn1 | inr _ => None end) p.
  Definition proj2_prog (p : prog) : mlanguage.prog Λ2 :=
    omap (λ fn, match fn with inl _ => None | inr fn2 => Some fn2 end) p.

  Implicit Types X : expr * state → Prop.

  Inductive head_step_mrel (p : prog) : expr * state → (expr * state → Prop) → Prop :=
  (* Internal step of an underlying module. *)
  | Step1S e1 σ1 privσ2 (X1 : _ → Prop) X :
    prim_step (proj1_prog p) (e1, σ1) X1 →
    (∀ e1' σ1', X1 (e1', σ1') → X (LkSE (Expr1 e1'), St1 σ1' privσ2)) →
    head_step_mrel p (LkSE (Expr1 e1), St1 σ1 privσ2) X
  | Step2S e2 σ2 privσ1 (X2 : _ → Prop) X :
    prim_step (proj2_prog p) (e2, σ2) X2 →
    (∀ e2' σ2', X2 (e2', σ2') → X (LkSE (Expr2 e2'), St2 privσ1 σ2')) →
    head_step_mrel p (LkSE (Expr2 e2), St2 privσ1 σ2) X
  (* Entering a function. Change the view of the heap in the process. *)
  | RunFunction1S σ1 pubσ privσ1 privσ2 fn1 args e1 X :
    mlanguage.apply_func fn1 args = Some e1 →
    linking.split_state σ1 pubσ privσ1 →
    X (LkSE (Expr1 e1), St1 σ1 privσ2) →
    head_step_mrel p (LkSE (RunFunction (inl fn1) args), St pubσ privσ1 privσ2) X
  | RunFunction2S σ2 pubσ privσ1 privσ2 fn2 arg e2 X :
    mlanguage.apply_func fn2 arg = Some e2 →
    linking.split_state σ2 pubσ privσ2 →
    X (LkSE (Expr2 e2), St2 privσ1 σ2) →
    head_step_mrel p (LkSE (RunFunction (inr fn2) arg), St pubσ privσ1 privσ2) X
  (* Producing a value when execution is finished *)
  | Val1S e1 v σ1 pubσ privσ1 privσ2 X :
    to_val e1 = Some v →
    linking.split_state σ1 pubσ privσ1 →
    X (LkSE (ExprV v), St pubσ privσ1 privσ2) →
    head_step_mrel p (LkSE (Expr1 e1), St1 σ1 privσ2) X
  | Val2S e2 v σ2 pubσ privσ1 privσ2 X :
    to_val e2 = Some v →
    linking.split_state σ2 pubσ privσ2 →
    X (LkSE (ExprV v), St pubσ privσ1 privσ2) →
    head_step_mrel p (LkSE (Expr2 e2), St2 privσ1 σ2) X
  (* Continuing execution by returning a value to its caller *)
  | Ret1S v k1 σ1 pubσ privσ1 privσ2 X :
    linking.split_state σ1 pubσ privσ1 →
    X (LkSE (Expr1 (mlanguage.fill k1 (of_val Λ1 v))), St1 σ1 privσ2) →
    head_step_mrel p (LkE (ExprV v) [inl k1], St pubσ privσ1 privσ2) X
  | Ret2S v k2 σ2 pubσ privσ1 privσ2 X :
    linking.split_state σ2 pubσ privσ2 →
    X (LkSE (Expr2 (mlanguage.fill k2 (of_val Λ2 v))), St2 privσ1 σ2) →
    head_step_mrel p (LkE (ExprV v) [inr k2], St pubσ privσ1 privσ2) X
  (* Stuck module calls bubble up as calls at the level of the linking module.
     (They may get unstuck then, if they match a function implemented by the
     other module.) *)
  | MakeCall1S k1 e1 fn_name arg σ1 pubσ privσ1 privσ2 X :
    mlanguage.to_class e1 = Some (commons.ExprCall fn_name arg) →
    proj1_prog p !! fn_name = None →
    linking.split_state σ1 pubσ privσ1 →
    X (LkE (ExprCall fn_name arg) [inl k1], St pubσ privσ1 privσ2) →
    head_step_mrel p (LkSE (Expr1 (mlanguage.fill k1 e1)), St1 σ1 privσ2) X
  | MakeCall2S k2 e2 fn_name arg σ2 pubσ privσ1 privσ2 X :
    mlanguage.to_class e2 = Some (commons.ExprCall fn_name arg) →
    proj2_prog p !! fn_name = None →
    linking.split_state σ2 pubσ privσ2 →
    X (LkE (ExprCall fn_name arg) [inr k2], St pubσ privσ1 privσ2) →
    head_step_mrel p (LkSE (Expr2 (mlanguage.fill k2 e2)), St2 privσ1 σ2) X
  (* Resolve an internal call to a module function *)
  | CallS fn_name fn arg σ X :
    p !! fn_name = Some fn →
    X (LkSE (RunFunction fn arg), σ) →
    head_step_mrel p (LkSE (ExprCall fn_name arg), σ) X.

  Program Definition head_step (p : prog) : umrel (expr * state) :=
    {| mrel := head_step_mrel p |}.
  Next Obligation.
    intros p. intros [[se k] σ] X Y Hstep HXY. inversion Hstep; subst;
      [ eapply Step1S | eapply Step2S | eapply RunFunction1S | eapply RunFunction2S
      | eapply Val1S | eapply Val2S | eapply Ret1S | eapply Ret2S
      | eapply MakeCall1S | eapply MakeCall2S | eapply CallS ]; eauto.
  Qed.

  Lemma mlanguage_mixin :
    MlanguageMixin (val:=val) of_class to_class empty_ectx comp_ectx fill
      apply_func head_step.
  Proof using.
    constructor.
    - intros c. destruct c; reflexivity.
    - intros e c. destruct e as [e k]. destruct e; cbn.
      1,2: destruct k. all: inversion 1; cbn; auto.
    - intros p v σ X. cbn. inversion 1.
    - intros p fn_name v σ X. split.
      + cbn. inversion 1; subst; naive_solver.
      + intros (fn & e2 & (? & Hfn & HX)). cbn.
        unfold apply_func in Hfn; simplify_eq. econstructor; eauto.
    - intros ? ? [? ?] ? ?. rewrite /fill /=. intros. simplify_eq/=; eauto.
    - intros [e k]. rewrite /fill /empty_ectx app_nil_r //.
    - intros K1 K2 [e k]. rewrite /fill /comp_ectx app_assoc //.
    - intros K [e1 k1] [e2 k2]. cbn. inversion 1; subst.
      rewrite (app_inv_tail K k1 k2) //.
    - intros K [e k]. unfold fill. intros Hsome.
      destruct (decide (K = empty_ectx)). by left. exfalso.
      assert (k ++ K ≠ []). { intros [? ?]%app_eq_nil. done. }
      cbn in Hsome. destruct (k ++ K) eqn:?.
      2: destruct e; by inversion Hsome. by destruct e.
    - intros p K' K_redex [e1' k1'] [e1_redex k1_redex] σ X.
      rewrite /fill. inversion 1; subst.
      destruct e1_redex; destruct k1' as [|u1' k1']; cbn; try by inversion 1.
      all: intros _; inversion 1; subst; unfold comp_ectx; cbn; eauto.
      all: naive_solver.
    - intros p K [e k] σ X. rewrite /fill. inversion 1; subst.
      all: try match goal with H : _ |- _ => symmetry in H; apply app_nil in H end.
      all: try match goal with H : _ |- _ => symmetry in H; apply app_singleton in H end.
      all: naive_solver.
  Qed.
End Linking.
End Link.

Arguments Link.ExprV {_ _ _} _.
Arguments Link.ExprCall {_ _ _} _ _.
Arguments Link.RunFunction {_ _ _} _ _.
Arguments Link.Expr1 {_ _ _} _.
Arguments Link.Expr2 {_ _ _} _.
Arguments Link.St {_ _ _ _ _ _} _ _ _.
Arguments Link.St1 {_ _ _ _ _ _} _ _.
Arguments Link.St2 {_ _ _ _ _ _} _ _.

Arguments Link.LkE {_ _ _} _ _.
Notation LkSE se := (Link.LkE se []).

Canonical Structure link_lang {val public_state} Λ1 Λ2 {lk1 lk2} : mlanguage val :=
  Mlanguage (@Link.mlanguage_mixin val public_state Λ1 Λ2 lk1 lk2).

Global Program Instance link_linkable
  {val public_state} (Λ1 Λ2 : mlanguage val)
  (lk1 : linkable Λ1 public_state)
  (lk2 : linkable Λ2 public_state) :
linkable (link_lang Λ1 Λ2) public_state := {
  linking.private_state := Link.private_state _ Λ1 Λ2;
  linking.split_state := Link.split_state _ Λ1 Λ2;
}.
Next Obligation.
  intros *. inversion 1; inversion 1; by simplify_eq.
Qed.
