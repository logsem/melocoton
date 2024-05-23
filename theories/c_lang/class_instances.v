From melocoton.language Require Export weakestpre lifting.
From melocoton.c_lang Require Export lang.
From melocoton.c_lang Require Import tactics notation.
From iris.prelude Require Import options.

Section pure_exec.
  Variable (p:language.prog C_lang).
  Local Ltac solve_exec_safe := intros; subst; do 2 eexists; try (repeat (econstructor; eauto); done).
  Local Ltac solve_exec_puredet := simpl; intros; inv_head_step; try done.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Local Ltac destruct_bool_decide := repeat (let H := fresh "Heq" in
    try destruct bool_decide eqn:H;
    [apply bool_decide_eq_true_1 in H| apply bool_decide_eq_false_1 in H]).

  Global Instance pure_unop op v v' :
    PureExec (un_op_eval op v = Some v') 1 p (UnOp op (Val v)) (Val v').
  Proof. solve_pure_exec. Qed.

  Global Instance pure_binop op v1 v2 v' :
    PureExec (bin_op_eval op v1 v2 = Some v') 1 p (BinOp op (Val v1) (Val v2)) (Val (LitV v')) | 10.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_if_true v e1 e2 : asTruth v = true ->
    PureExec True 1 p (If (Val $ v) e1 e2) e1.
  Proof. intros H. solve_pure_exec. congruence. Qed.
  Global Instance pure_if_non_zero (v0:Z) e1 e2 : v0 ≠ 0%Z ->
    PureExec True 1 p (If (Val $ LitV $ LitInt v0) e1 e2) e1.
  Proof. intros H. apply pure_if_true. destruct v0; cbn; congruence. Qed.
  Global Instance pure_if_true_bool e1 e2 :
    PureExec True 1 p (If (Val $ LitV $ LitBool true) e1 e2) e1.
  Proof. apply pure_if_true. easy. Qed.
  Global Instance pure_if_false v e1 e2 : asTruth v = false ->
    PureExec True 1 p (If (Val $ v) e1 e2) e2.
  Proof. intros H. solve_pure_exec. congruence. Qed.
  Global Instance pure_if_zero e1 e2 :
    PureExec True 1 p (If (Val $ LitV $ LitInt (0%Z)) e1 e2) e2.
  Proof. apply pure_if_false. easy. Qed.
  Global Instance pure_if_false_bool e1 e2 :
    PureExec True 1 p (If (Val $ LitV $ LitBool false) e1 e2) e2.
  Proof. apply pure_if_zero. Qed.

  Global Instance pure_while e1 e2 :
    PureExec True 1 p (While e1 e2) (If e1 (Let BAnon e2 (While e1 e2)) (Val $ LitV $ LitInt 0)).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_let x v1 e2 :
    PureExec True 1 p (Let x (Val v1) e2) (subst x v1 e2).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_funcall s va args res e :
    PureExec
      ((p : gmap.gmap string function) !! s = Some (Fun args e)
      ∧ apply_function (Fun args e) va = Some res)
      1 p (FunCall (Val $ LitV $ LitFunPtr s) (map Val va)) res.
  Proof. solve_pure_exec; destruct H as [H1 H2].
    - econstructor; first done. rewrite H2. reflexivity.
    - simplify_eq. repeat split.
  Qed.

End pure_exec.
