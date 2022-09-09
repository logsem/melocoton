From melocoton.language Require Import mlanguage.
From melocoton.c_toy_mlang Require Export lang.
From melocoton.c_toy_mlang Require Import tactics notation.
From melocoton.c_toy_mlang Require Import lang_instantiation.
From iris.prelude Require Import options.

Global Instance into_val_val v : @IntoVal C_mlang_melocoton (Val v) v.
Proof. done. Qed.
Global Instance as_val_val v : @AsVal C_mlang_melocoton (Val v).
Proof. by eexists. Qed.

Lemma clang_sub_redexes_are_values e :
  (∀ Ki e', e = fill_item Ki e' → is_Some (mlanguage.to_val e')) →
  sub_redexes_are_values e.
Proof.
  intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
  intros []%eq_None_not_Some.
  eapply mlanguage.fill_val, Hsub. by rewrite /= fill_app.
Qed.

(** * Instances of the [Atomic] class *)
Section atomic.
  Context {p:program}.

  Local Ltac solve_atomic :=
    apply mlanguage_atomic;
      [intros H1 H2 H3 Hstep; inversion Hstep; try naive_solver; congruence
      |apply clang_sub_redexes_are_values; intros [] **; naive_solver].

  (** The instance below is a more general version of [Skip] *)
  Global Instance let_atomic x v1 v2 : Atomic (Let x (Val v1) (Val v2)).
  Proof.
    apply mlanguage_atomic.
    { intros ? ? ? Hstep. inversion Hstep; subst.

      [intros H1 H2 H3 Hstep; inversion Hstep; try naive_solver; congruence
      |apply clang_sub_redexes_are_values; intros [] **; naive_solver].


    destruct x; solve_atomic. Qed.
  Global Instance unop_atomic op v : Atomic (UnOp op (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance binop_atomic op v1 v2 : Atomic (BinOp op (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance if_true_atomic v v1 e2 : asTruth v = true ->
    Atomic (If (Val $ v) (Val v1) e2).
  Proof. intros H. solve_atomic. Qed.
  Global Instance if_non_zero_atomic (v0:Z) v1 e2 : v0 ≠ 0%Z ->
    Atomic (If (Val $ LitV $ LitInt v0) (Val v1) e2).
  Proof. intros H. apply if_true_atomic. destruct v0; cbn; congruence. Qed.
  Global Instance if_true_bool_atomic v1 e2 :
    Atomic (If (Val $ LitV $ LitBool true) (Val v1) e2).
  Proof. intros H. apply if_true_atomic. easy. Qed.
  Global Instance if_false_atomic v e1 v2 : asTruth v = false ->
    Atomic (If (Val $ v) e1 (Val v2)).
  Proof. intros H. solve_atomic. Qed.
  Global Instance if_zero_atomic e1 v2 :
    Atomic (If (Val $ LitV $ LitInt (0%Z)) e1 (Val v2)).
  Proof. intros H. apply if_false_atomic. easy. Qed.
  Global Instance if_false_bool_atomic e1 v2 :
    Atomic (If (Val $ LitV $ LitBool false) e1 (Val v2)).
  Proof. intros H. apply if_false_atomic. easy. Qed.

  Global Instance alloc_atomic v : Atomic (Malloc (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance free_atomic v1 v2 : Atomic (Free (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.
  Global Instance load_atomic v : Atomic (Load (Val v)).
  Proof. solve_atomic. Qed.
  Global Instance store_atomic v1 v2 : Atomic (Store (Val v1) (Val v2)).
  Proof. solve_atomic. Qed.

End atomic.

Section pure_exec.
  Context {p:program}.
  (* Local Ltac solve_exec_safe := intros; subst; do 4 eexists; try (econstructor; eauto; done). *)
  (* Local Ltac solve_exec_puredet := simpl; intros; inv_head_step; try done. *)
  (* Local Ltac solve_pure_exec := *)
  (*   subst; intros ?; apply nsteps_once, pure_head_step_pure_step; *)
  (*     constructor; [solve_exec_safe | solve_exec_puredet]. *)

  Local Ltac solve_exec_safe :=
    intros; subst; try (exists (λ _, True); econstructor; eauto; done).
  Local Ltac solve_exec_puredet :=
    intros; cbn; try (econstructor; by eauto).
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply multirelations.repeat_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Local Ltac destruct_bool_decide := repeat (let H := fresh "Heq" in
    try destruct bool_decide eqn:H;
    [apply bool_decide_eq_true_1 in H| apply bool_decide_eq_false_1 in H]).

  Global Instance pure_let x (v1 v2 : val) :
    PureExec True 1 p (Let x (Val v1) (Val v2)) (singl (subst' x v1 v2)).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_unop op v v' :
    PureExec (un_op_eval op v = Some v') 1 p (UnOp op (Val v)) (singl (Val v')).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_binop op v1 v2 v' :
    PureExec (bin_op_eval op v1 v2 = Some v') 1 p (BinOp op (Val v1) (Val v2)) (singl (Val (LitV v'))) | 10.
  Proof. solve_pure_exec. Qed.

  (* Higher-priority instance for [EqOp]. *)
  Global Instance pure_eqop v1 v2 :
    PureExec (vals_compare_safe v1 v2) 1 p
      (BinOp EqOp (Val (LitV v1)) (Val (LitV v2)))
      (singl (Val $ LitV $ LitBool $ bool_decide (v1 = v2))) | 1.
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
    PureExec True 1 p (If (Val $ v) e1 e2) (singl e1).
  Proof. intros H. solve_pure_exec. Qed.
  Global Instance pure_if_non_zero (v0:Z) e1 e2 : v0 ≠ 0%Z ->
    PureExec True 1 p (If (Val $ LitV $ LitInt v0) e1 e2) (singl e1).
  Proof. intros H. apply pure_if_true. destruct v0; cbn; congruence. Qed.
  Global Instance pure_if_true_bool e1 e2 :
    PureExec True 1 p (If (Val $ LitV $ LitBool true) e1 e2) (singl e1).
  Proof. apply pure_if_true. easy. Qed.
  Global Instance pure_if_false v e1 e2 : asTruth v = false ->
    PureExec True 1 p (If (Val $ v) e1 e2) (singl e2).
  Proof. intros H. solve_pure_exec. Qed.
  Global Instance pure_if_zero e1 e2 :
    PureExec True 1 p (If (Val $ LitV $ LitInt (0%Z)) e1 e2) (singl e2).
  Proof. apply pure_if_false. easy. Qed.
  Global Instance pure_if_false_bool e1 e2 :
    PureExec True 1 p (If (Val $ LitV $ LitBool false) e1 e2) (singl e2).
  Proof. apply pure_if_zero. Qed.

  Global Instance pure_while e1 e2 :
    PureExec True 1 p (While e1 e2) (singl (If e1 (Let BAnon e1 (While e1 e2)) (Val $ LitV $ LitInt 0))).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_funcall s va args res e :
    PureExec ((p : gmap.gmap string function) !! s = Some (Fun args e) ∧ zip_args args va = Some res) 1 p
             (FunCall (Val $ LitV $ LitFunPtr s) (map Val va))
             (singl (subst_all res e)).
  Proof.
    solve_pure_exec; destruct H as [H1 H2].
    { exists (λ _, True). econstructor; eauto.
      rewrite /apply_function H2//. }
    { econstructor; eauto.
      - rewrite /apply_function H2//.
      - rewrite /singl //. }
  Qed.

End pure_exec.
