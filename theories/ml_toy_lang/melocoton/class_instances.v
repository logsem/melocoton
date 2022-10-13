From melocoton.language Require Export language weakestpre lifting.
From melocoton.ml_toy_lang Require Export melocoton.lang_instantiation lang.
From melocoton.ml_toy_lang Require Import tactics melocoton.tactics notation lang.
From iris.prelude Require Import options.
Import ml_toy_lang.

(** * Instances of the [PureExec] class *)
(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)

Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

Section pure_exec.
  Context  {p:ml_program}.
  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; try (repeat (econstructor; eauto); done).
  Local Ltac solve_exec_puredet := simpl; intros; inv_head_step; try inv_head_step; try done.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_recc f x (erec : expr) :
    PureExec True 1 p (Rec f x erec) (Val $ RecV f x erec).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_pairc (v1 v2 : val) :
    PureExec True 1 p (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injlc (v : val) :
    PureExec True 1 p (InjL $ Val v) (Val $ InjLV v).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injrc (v : val) :
    PureExec True 1 p (InjR $ Val v) (Val $ InjRV v).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
    PureExec True 1 p (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
  Proof. unfold AsRecV in *. solve_pure_exec. Qed.

  Global Instance pure_unop op v v' :
    PureExec (un_op_eval op v = Some v') 1 p (UnOp op (Val v)) (Val v').
  Proof. solve_pure_exec. Qed.

  Global Instance pure_binop op v1 v2 v' :
    PureExec (bin_op_eval op v1 v2 = Some v') 1 p (BinOp op (Val v1) (Val v2)) (Val v') | 10.
  Proof. solve_pure_exec. Qed.
  (* Lower-cost instance for [EqOp]. *)
  Global Instance pure_eqop v1 v2 :
    PureExec (vals_compare_safe v1 v2) 1 p
      (BinOp EqOp (Val v1) (Val v2))
      (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
  Proof.
    intros Hcompare.
    cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
    { intros. revert Hcompare. solve_pure_exec. }
    rewrite /bin_op_eval /= decide_True //.
  Qed.

  Global Instance pure_if_true e1 e2 :
    PureExec True 1 p (If (Val $ LitV $ LitBool true) e1 e2) e1.
  Proof. solve_pure_exec. Qed.
  Global Instance pure_if_false e1 e2 :
    PureExec True 1 p (If (Val $ LitV  $ LitBool false) e1 e2) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst v1 v2 :
    PureExec True 1 p (Fst (Val $ PairV v1 v2)) (Val v1).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_snd v1 v2 :
    PureExec True 1 p (Snd (Val $ PairV v1 v2)) (Val v2).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl v e1 e2 :
    PureExec True 1 p (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_case_inr v e1 e2 :
    PureExec True 1 p (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_funcall s va f res : 
    PureExec ((p : gmap.gmap string ml_function) !! s = Some f ∧ apply_function f va = Some res) 1 p (Extern s (map Val va)) res.
  Proof. destruct f.
         subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
         constructor; [solve_exec_safe | solve_exec_puredet].
         + econstructor. destruct H. econstructor; done.
         + repeat split; try congruence. destruct H as [H1 H2]. rewrite H3 in H1.
           assert (args = b) as -> by congruence.
           assert (e = e0) as -> by congruence.
           congruence.
  Qed.
End pure_exec.
