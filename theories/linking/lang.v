From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton.mlanguage Require Import mlanguage.
From iris.algebra Require Import stepindex.

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

  Definition cont : Type :=
    list (Λ1.(cont) + Λ2.(cont)).

  (* expr need to be wrapped in a fresh inductive for the language canonical
     structure to work when using WP *)
  Inductive expr : Type :=
    LkE (se: simple_expr) (k: cont).

  Definition private_state : Type :=
    (lk1.(private_state) * lk2.(private_state)).

  Inductive state : Type :=
    | St (pubσ : public_state)
             (privσ1 : lk1.(mlanguage.private_state))
             (privσ2 : lk2.(mlanguage.private_state))
    | St1 (σ1 : Λ1.(mlanguage.state)) (privσ2 : lk2.(mlanguage.private_state))
    | St2 (privσ1 : lk1.(mlanguage.private_state)) (σ2 : Λ2.(mlanguage.state)).

  Inductive split_state : state → public_state → private_state → Prop :=
    | LinkSplitSt pubσ privσ1 privσ2 :
      split_state (St pubσ privσ1 privσ2) pubσ (privσ1, privσ2).

  Definition of_val (v:val) : expr := LkE (ExprV v) [].
  Definition to_val (e:expr) : option val := match e with
    LkE (ExprV v) [] => Some v
  | _ => None end.

  Definition comp_cont (K1 K2 : cont) : cont :=
    K2 ++ K1.

  Definition resume_with (K : cont) (e : expr) : expr :=
    let 'LkE se k := e in
    LkE se (k ++ K).

  Definition apply_func (fn : func) (args : list val) : option expr :=
    Some (LkE (RunFunction fn args) []).

  Definition is_call e (fn_name:string) args C := e = LkE (ExprCall fn_name args) C.

  Local Notation prog := (gmap string func).

  Definition proj1_prog (p : prog) : mlanguage.prog Λ1 :=
    omap (λ fn, match fn with inl fn1 => Some fn1 | inr _ => None end) p.
  Definition proj2_prog (p : prog) : mlanguage.prog Λ2 :=
    omap (λ fn, match fn with inl _ => None | inr fn2 => Some fn2 end) p.

  Implicit Types X : expr * state → Prop.

  Inductive prim_step_mrel (p : prog) : expr * state → (expr * state → Prop) → Prop :=
  (* Internal step of an underlying module. *)
  | Step1S e1 C σ1 privσ2 (X1 X : _ → Prop) :
    mlanguage.to_val e1 = None →
    mlanguage.prim_step (proj1_prog p) (e1, σ1) X1 →
    (∀ e1' σ1',
      X1 (e1', σ1') →
      X (LkE (Expr1 e1') C, St1 σ1' privσ2)) →
    prim_step_mrel p (LkE (Expr1 e1) C, St1 σ1 privσ2) X
  | Step2S e2 C σ2 privσ1 (X2 X : _ → Prop) :
    mlanguage.to_val e2 = None →
    mlanguage.prim_step (proj2_prog p) (e2, σ2) X2 →
    (∀ e2' σ2',
       X2 (e2', σ2') →
       X (LkE (Expr2 e2') C, St2 privσ1 σ2')) →
    prim_step_mrel p (LkE (Expr2 e2) C, St2 privσ1 σ2) X
  (* Stuck module calls bubble up as calls at the level of the linking module.
     (They may get unstuck then, if they match a function implemented by the
     other module.) *)
  | MakeCall1S e1 C σ1 pubσ privσ1 privσ2 fn_name arg k1 X :
    mlanguage.is_call e1 fn_name arg k1 →
    proj1_prog p !! fn_name = None →
    mlanguage.split_state σ1 pubσ privσ1 →
    X (LkE (ExprCall fn_name arg) (inl k1 :: C), St pubσ privσ1 privσ2) →
    prim_step_mrel p (LkE (Expr1 e1) C, St1 σ1 privσ2) X
  | MakeCall2S e2 C σ2 pubσ privσ1 privσ2 fn_name arg k2 X :
    mlanguage.is_call e2 fn_name arg k2 →
    proj2_prog p !! fn_name = None →
    mlanguage.split_state σ2 pubσ privσ2 →
    X (LkE (ExprCall fn_name arg) (inr k2 :: C), St pubσ privσ1 privσ2) →
    prim_step_mrel p (LkE (Expr2 e2) C, St2 privσ1 σ2) X
  (* Producing a value when execution is finished *)
  | Val1S e1 C σ1 v pubσ privσ1 privσ2 X :
    mlanguage.to_val e1 = Some v →
    (* Splitting the state is angelic, the underlying language can choose a concrete splitting. *)
    (* If no such splitting exists, we have UB *)
    mlanguage.split_state σ1 pubσ privσ1 →
    X (LkE (ExprV v) C, St pubσ privσ1 privσ2) →
    prim_step_mrel p (LkE (Expr1 e1) C, St1 σ1 privσ2) X
  | Val2S e2 C σ2 v pubσ privσ1 privσ2 X :
    mlanguage.to_val e2 = Some v →
    (* Splitting the state is angelic, the underlying language can choose a concrete splitting. *)
    (* If no such splitting exists, we have UB *)
    mlanguage.split_state σ2 pubσ privσ2 →
    X (LkE (ExprV v) C, St pubσ privσ1 privσ2) →
    prim_step_mrel p (LkE (Expr2 e2) C, St2 privσ1 σ2) X
  (* Entering a function. Change the view of the heap in the process.
     Merging the state is angelic. *)
  | RunFunction1S fn1 args C e1 σ1 pubσ privσ1 privσ2 X :
    mlanguage.apply_func fn1 args = Some e1 →
    mlanguage.split_state σ1 pubσ privσ1 →
    X (LkE (Expr1 e1) C, St1 σ1 privσ2) →
    prim_step_mrel p (LkE (RunFunction (inl fn1) args) C, St pubσ privσ1 privσ2) X
  | RunFunction2S fn2 args C e2 σ2 pubσ privσ1 privσ2 X :
    mlanguage.apply_func fn2 args = Some e2 →
    mlanguage.split_state σ2 pubσ privσ2 →
    X (LkE (Expr2 e2) C, St2 privσ1 σ2) →
    prim_step_mrel p (LkE (RunFunction (inr fn2) args) C, St pubσ privσ1 privσ2) X
  (* Continuing execution by returning a value to its caller. *)
  | Ret1S v k1 C σ1 pubσ privσ1 privσ2 X :
    mlanguage.split_state σ1 pubσ privσ1 →
    X (LkE (Expr1 (mlanguage.resume_with k1 (mlanguage.of_val Λ1 v))) C, St1 σ1 privσ2) →
    prim_step_mrel p (LkE (ExprV v) (inl k1 :: C), St pubσ privσ1 privσ2) X
  | Ret2S v k2 C σ2 pubσ privσ1 privσ2 X :
    mlanguage.split_state σ2 pubσ privσ2 →
    X (LkE (Expr2 (mlanguage.resume_with k2 (mlanguage.of_val Λ2 v))) C, St2 privσ1 σ2) →
    prim_step_mrel p (LkE (ExprV v) (inr k2 :: C), St pubσ privσ1 privσ2) X
  (* Resolve an internal call to a module function *)
  | CallS fn_name fn arg σ C X :
    p !! fn_name = Some fn →
    X (LkE (RunFunction fn arg) C, σ) →
    prim_step_mrel p (LkE (ExprCall fn_name arg) C, σ) X
  (* Terminate execution with NB on values *)
  | ValStopS v σ X :
    prim_step_mrel p (LkE (ExprV v) [], σ) X.

  Program Definition prim_step (p : prog) : umrel (expr * state) :=
    {| mrel := prim_step_mrel p |}.
  Next Obligation.
    intros p. intros [[se k] σ] X Y Hstep HXY. inversion Hstep; subst;
      [ eapply Step1S | eapply Step2S | eapply MakeCall1S | eapply MakeCall2S
      | eapply Val1S | eapply Val2S | eapply RunFunction1S | eapply RunFunction2S
      | eapply Ret1S | eapply Ret2S | eapply CallS | eapply ValStopS ];
      eauto; naive_solver.
  Qed.

  Lemma mlanguage_mixin :
    MlanguageMixin (val:=val) of_val to_val is_call resume_with comp_cont
      apply_func prim_step.
  Proof using.
    constructor.
    - intros v. done.
    - intros e c. destruct e as [e [|]]; destruct e; cbn; intros; by simplify_eq.
    - intros *. eapply ValStopS.
    - intros p e fn_name arg C σ X ->. split.
      + inversion 1; simplify_eq. do 2 eexists. repeat split; eauto.
      + intros (?&[]&?&?&?). unfold apply_func in *. simplify_eq.
        econstructor; eauto.
    - intros e [v Hv] f vs C ->. done.
    - intros ? C1 C2 s vv ->. cbn. done.
    - intros [] C [v Hv]; cbn in Hv. repeat case_match; simplify_eq.
      apply app_eq_nil in H0 as [-> ->]. done.
    - intros [] C1 C2. rewrite /= app_assoc //.
    - intros p C [es eC] σ X Hnv. inversion 1; simplify_eq.
      1,2: econstructor; eauto; intros; eexists (LkE _ _); by eauto. (* StepS *)
      { eapply MakeCall1S; eauto; eexists (LkE _ _); split; eauto;
          unfold resume_with; by eauto. }
      { eapply MakeCall2S; eauto; eexists (LkE _ _); split; eauto;
          unfold resume_with; by eauto. }
      { eapply Val1S; eauto. eexists (LkE _ _). split; eauto. }
      { eapply Val2S; eauto. eexists (LkE _ _). split; eauto. }
      1,2: econstructor; eauto; eexists (LkE _ _); split; eauto. (* RunFunctionS *)
      1,2: econstructor; eauto; eexists (LkE _ _); split; eauto. (* RetS *)
      eapply CallS; eauto; eexists (LkE _ _); split; eauto.
    - intros p [[] eC] σ Hnv; simplify_eq;
        try by (intros _; inversion 1; simplify_eq; eauto).
      + destruct eC as [|[] eC']; first done; intros _;
          inversion 1; simplify_eq; eauto.
      + intros _. inversion 1; simplify_eq; eauto.
        eapply prim_step_no_NB in H5 as (e1 & σ1' & ?); eauto.
      + intros _. inversion 1; simplify_eq; eauto.
        eapply prim_step_no_NB in H5 as (e2 & σ2' & ?); eauto.
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
  mlanguage.private_state := Link.private_state _ Λ1 Λ2;
  mlanguage.split_state := Link.split_state _ Λ1 Λ2;
}.

Definition link_prog {val public_state} (Λ1 Λ2 : mlanguage val)
  {lk1 : linkable Λ1 public_state} {lk2 : linkable Λ2 public_state}
  (p1 : mlang_prog Λ1) (p2 : mlang_prog Λ2) :
mlang_prog (link_lang Λ1 Λ2) :=
  fmap inl p1 ∪ fmap inr p2.
