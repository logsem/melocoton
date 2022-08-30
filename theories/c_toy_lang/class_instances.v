From iris.program_logic Require Export language.
From melocoton.c_toy_lang Require Export lang.
From melocoton.c_toy_lang Require Import tactics notation.
From iris.prelude Require Import options.

Global Instance into_val_val (p:program) v : @IntoVal (C_lang p) (Val v) v.
Proof. done. Qed.
Global Instance as_val_val p v : @AsVal (C_lang p) (Val v).
Proof. by eexists. Qed.

(** * Instances of the [Atomic] class *)
Section atomic.
  Context {p:program}.
  Local Ltac solve_atomic :=
    apply strongly_atomic_atomic, ectx_language_atomic;
      [intros H1 H2 H3 H4 H5 H6%bogo_head_step_elim; inversion H6; try naive_solver; congruence
      |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

  (** The instance below is a more general version of [Skip] *)
  Global Instance let_atomic s x v1 v2 : Atomic s (Let x (Val v1) (Val v2)).
  Proof. destruct x; solve_atomic. Qed.
  Global Instance unop_atomic s op v : Atomic s (UnOp op (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance if_true_atomic s v v1 e2 : asTruth v = true ->
    Atomic s (If (Val $ v) (Val v1) e2).
  Proof. intros H. solve_atomic. Qed.
  Global Instance if_non_zero_atomic s (v0:Z) v1 e2 : v0 ≠ 0%Z ->
    Atomic s (If (Val $ LitV $ LitInt v0) (Val v1) e2).
  Proof. intros H. apply if_true_atomic. destruct v0; cbn; congruence. Qed.
  Global Instance if_true_bool_atomic s v1 e2 :
    Atomic s (If (Val $ LitV $ LitBool true) (Val v1) e2).
  Proof. intros H. apply if_true_atomic. easy. Qed.
  Global Instance if_false_atomic s v e1 v2 : asTruth v = false ->
    Atomic s (If (Val $ v) e1 (Val v2)).
  Proof. intros H. solve_atomic. Qed.
  Global Instance if_zero_atomic s e1 v2 : 
    Atomic s (If (Val $ LitV $ LitInt (0%Z)) e1 (Val v2)).
  Proof. intros H. apply if_false_atomic. easy. Qed.
  Global Instance if_false_bool_atomic s e1 v2 :
    Atomic s (If (Val $ LitV $ LitBool false) e1 (Val v2)).
  Proof. intros H. apply if_false_atomic. easy. Qed.

  Global Instance alloc_atomic s v : Atomic s (Malloc (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance free_atomic s v1 v2 : Atomic s (Free (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance load_atomic s v : Atomic s (Load (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.

End atomic.

Section pure_exec.
  Context {p:program}.
  Local Ltac solve_exec_safe := intros; subst; do 4 eexists; try (econstructor; eauto; done).
  Local Ltac solve_exec_puredet := simpl; intros; inv_head_step; try done.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Local Ltac destruct_bool_decide := repeat (let H := fresh "Heq" in 
    try destruct bool_decide eqn:H; 
    [apply bool_decide_eq_true_1 in H| apply bool_decide_eq_false_1 in H]).

  Global Instance pure_let x (v1 v2 : val) :
    PureExec True 1 (Let x (Val v1) (Val v2)) (subst' x v1 v2).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_unop op v v' :
    PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
  Proof. solve_pure_exec. Qed.

  Global Instance pure_binop op v1 v2 v' :
    PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val (LitV v')) | 10.
  Proof. solve_pure_exec. Qed.

  (* Higher-priority instance for [EqOp]. *)
  Global Instance pure_eqop v1 v2 :
    PureExec (vals_compare_safe v1 v2) 1
      (BinOp EqOp (Val (LitV v1)) (Val (LitV v2)))
      (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
  Proof.
    intros Hcompare.
    cut (bin_op_eval EqOp (LitV v1) (LitV v2) = Some $ LitBool $ bool_decide (v1 = v2)).
    { intros. revert Hcompare. solve_pure_exec. }
    destruct v1, v2; cbn in *; try easy.
    - destruct_bool_decide; congruence.
    - destruct l, l0. destruct_bool_decide; congruence.
    - destruct_bool_decide; congruence.
  Qed.

  Global Instance pure_if_true v e1 e2 : asTruth v = true ->
    PureExec True 1 (If (Val $ v) e1 e2) e1.
  Proof. intros H. solve_pure_exec. congruence. Qed.
  Global Instance pure_if_non_zero (v0:Z) e1 e2 : v0 ≠ 0%Z ->
    PureExec True 1 (If (Val $ LitV $ LitInt v0) e1 e2) e1.
  Proof. intros H. apply pure_if_true. destruct v0; cbn; congruence. Qed.
  Global Instance pure_if_true_bool e1 e2 :
    PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
  Proof. apply pure_if_true. easy. Qed.
  Global Instance pure_if_false v e1 e2 : asTruth v = false ->
    PureExec True 1 (If (Val $ v) e1 e2) e2.
  Proof. intros H. solve_pure_exec. congruence. Qed.
  Global Instance pure_if_zero e1 e2 : 
    PureExec True 1  (If (Val $ LitV $ LitInt (0%Z)) e1 e2) e2.
  Proof. apply pure_if_false. easy. Qed.
  Global Instance pure_if_false_bool e1 e2 :
    PureExec True 1  (If (Val $ LitV $ LitBool false) e1 e2) e2.
  Proof. apply pure_if_zero. Qed.

  Global Instance pure_while e1 e2 : 
    PureExec True 1 (While e1 e2) (If e1 (Let BAnon e1 (While e1 e2)) (Val $ LitV $ LitInt 0)).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_funcall s va args res e : 
    PureExec ((p : gmap.gmap string function) !! s = Some (Fun args e) ∧ zip_args args va = Some res) 1 (FunCall (Val $ LitV $ LitFunPtr s) (map Val va)) (subst_all res e).
  Proof. solve_pure_exec; destruct H as [H1 H2]. 1: by econstructor. repeat split; congruence. Qed.
End pure_exec.
