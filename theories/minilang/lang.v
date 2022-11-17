From stdpp Require Import strings gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.
From melocoton.mlanguage Require Import mlanguage.

Module Mini_lang.

Definition loc := nat.

Inductive instr :=
  | Read (l : loc)
  | Write (l : loc)
  | Register (l : loc)
  | Const (n : nat)
  | Call (fn : string) (n : nat (*ignored*)).

Inductive expr := E (ii : list instr).

Definition of_class (c : mixin_expr_class unit) : expr :=
  match c with
  | ExprVal _ => E []
  | ExprCall fn l => E [ Call fn (List.length l) ]
  end.

Definition to_class (e : expr) : option (mixin_expr_class unit) :=
  match e with
  | E [] => Some (ExprVal tt)
  | E [ Call fn n ] => Some (ExprCall fn (repeat tt n))
  | _ => None
  end.

Definition app_expr : expr → expr → expr :=
  λ '(E ii1) '(E ii2), E (ii1 ++ ii2).

Local Notation prog := (gmap string expr).

Definition state : Type := gmap loc nat * nat.
Definition private_state : Type := gset loc.
Definition public_state : Type := gmap loc nat * nat.

Inductive split_state : state → public_state → private_state → Prop :=
  | SplitState store acc locs :
    locs ⊆ dom store →
    split_state (store, acc) (store, acc) locs.

Implicit Types X : expr * state → Prop.
Inductive head_step_mrel (p: prog) : expr * state → (expr * state → Prop) → Prop :=
  | ReadS l store acc n X :
    store !! l = Some n →
    X (E [], (store, n)) →
    head_step_mrel p (E [Read l], (store, acc)) X
  | WriteS l store acc X :
    l ∈ dom store →
    X (E [], (<[ l := acc ]> store, acc)) →
    head_step_mrel p (E [Write l], (store, acc)) X
  | RegisterS l store acc X :
    l ∉ dom store →
    X (E [], (<[ l := 0 ]> store, acc)) →
    head_step_mrel p (E [Register l], (store, acc)) X
  | ConstS n store acc X :
    X (E [], (store, n)) →
    head_step_mrel p (E [Const n], (store, acc)) X
  | CallS fn n e' st X :
    p !! fn = Some e' →
    X (e', st) →
    head_step_mrel p (E [Call fn n], st) X.

Program Definition head_step (p: prog) : umrel (expr * state) :=
  {| mrel := head_step_mrel p |}.
Next Obligation.
  intros ? ? ? ?.
  inversion 1; intros; simplify_eq/=;
    econstructor; naive_solver.
Qed.

Lemma middle_not_eq_nil {A} (l:list A) x l' :
  l ++ x :: l' ≠ [].
Proof. by destruct l. Qed.

Lemma repeat_tt_eq (l : list unit) :
  repeat tt (length l) = l.
Proof.
  induction l as [|[] ? IHl]; simpl; try done.
  by rewrite IHl.
Qed.

Lemma mlang_mixin :
  @MlanguageMixin expr unit expr expr public_state private_state state
                  of_class to_class
                  (E[]) (λ K K', app_expr K' K) (λ K e, app_expr e K)
                  split_state (λ e _, Some e) head_step.
Proof.
  econstructor.
  - intros [[]|?]; simpl; try done. rewrite repeat_tt_eq //.
  - intros [ii] [[]|?]; simpl.
    + destruct ii as [| [] ?]; simpl; try by inversion 1.
      all: destruct ii; try by inversion 1.
    + destruct ii as [| [] ?]; simpl; try by inversion 1.
      all: destruct ii; try by inversion 1. intro; simplify_eq.
      rewrite repeat_length//.
  - intros p [] σ X. simpl. inversion 1.
  - intros p f vs σ X. split.
    + simpl. inversion 1; simplify_eq. naive_solver.
    + intros (?&?&?&?&?); simplify_eq/=. econstructor; eauto.
  - intros [K] [K'] [ii] f vs. simpl. intros HH. simplify_eq.
    destruct ii; first (right; done); left. simpl in HH.
    inversion HH; subst. eexists (E _). done.
  - intros ? ? [? ?] ?. inversion 1; inversion 1; by simplify_eq.
  - intros [ii]. rewrite /= app_nil_r//.
  - intros [] [] []. simpl. rewrite app_assoc//.
  - intros [] [] []. simpl. intro HH. simplify_eq. apply app_inv_tail in HH. by subst.
  - intros [] []. cbn [app_expr]. destruct ii.
    + intros _. by left.
    + cbn [app]. simpl. intros. right. exists tt.
      repeat (case_match; simplify_eq; try rewrite -> app_nil_r in * ; simplify_eq);
        try by inversion H;
        try match goal with H : _ |- _ => by apply middle_not_eq_nil in H end.
  - intros p [K'] [K] [e1'] [e1] σ X. cbn [app_expr]. intros Happ Hclass Hstep.
    simplify_eq.
    destruct e1' as [|i e1']; first by inversion Hclass. exists (E e1').
    inversion Hstep; simplify_eq/=; done.
  - intros p [K] [e] σ X Hstep. destruct K as [|i K]; first (left; done).
    right. exists tt. simpl in Hstep. destruct e as [|i' e]; first done.
    simpl in Hstep. inversion Hstep; simplify_eq.
    all: match goal with H : [] = _ ++ _ :: _ |- _ =>
           symmetry in H; by apply middle_not_eq_nil in H end.
Qed.

End Mini_lang.
Export Mini_lang.

Canonical Structure minilang : mlanguage _ _ := Mlanguage Mini_lang.mlang_mixin.
