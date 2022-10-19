From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From melocoton.c_toy_lang Require Import lang notation melocoton.proofmode.
From iris.prelude Require Import options.
Import uPred.


(** Heap tactics *)
Section examples.

Context `{!heapGS Σ}.
 
Fixpoint fib (n:nat) : nat := match n with
  0 => 0
| S n' => match n' with 
      0 => 1
    | S n'' => fib n' + fib n'' end end.

Definition fib_prog name (x:expr) := (if: "x" < #2 then "x" else (call: (&name) with ("x" - #1))
           + (call: (&name) with ("x" - #2) ))%E.
Definition heap_example := (let: "x" := malloc (#2) in 
                            (("x" +ₗ #1) <- #42 ;;
                             ("x" +ₗ #0) <- #1337 ;;
                             free ("x" +ₗ #1, #1) ;;
                             *"x"))%E.
Definition fib_func name : function := Fun [BNamed "x"] (fib_prog name "x").
Definition exampleProgram name : gmap string function :=
  insert "fib" (fib_func name) ∅.

Definition exampleEnv name : prog_environ := {|
  weakestpre.prog := exampleProgram name;
  T := λ s v wp, match (s,v) with
      ("fiba", [ #(LitInt z) ]) => wp (#(fib (Z.to_nat z)))
    | _ => ⌜False⌝%I end
|}.

(* A simple recursive function *)

Lemma fib_prog_correct (n:nat)
  : ⊢ (WP (call: &"fib" with (Val #n)) @ exampleEnv "fib"; ⊤ {{ v, ⌜v = #(fib n)⌝ }}).
Proof.
  iStartProof.
  iLöb as "IH" forall (n).
  wp_pures.
  destruct (bool_decide _) eqn:Heq.
  - wp_pures. iModIntro. apply bool_decide_eq_true in Heq.
    assert (n=0 \/ n=1) as [-> | ->] by lia; done.
  - do 2 wp_pure _. apply bool_decide_eq_false in Heq. wp_bind (FunCall _ _).
    wp_apply wp_wand.
    { assert ((n-1)%Z=(n-1)%nat) as -> by lia. iApply "IH". }
    iIntros (v) "->". wp_bind (FunCall _ _). wp_pure _. wp_apply wp_wand.
    { assert ((n-2)%Z=(n-2)%nat) as -> by lia. iApply "IH". }
    iIntros (v) "->". wp_pures. iModIntro. iPureIntro. rewrite <- Nat2Z.inj_add.
    repeat f_equal.
    assert (n = S (S (n-2))) as -> by lia.
    cbn. do 2 f_equal. lia.
Qed.

(* A call to an axiomatically specified function *)


Lemma fiba_prog_correct (n:nat)
  : ⊢ (WP (call: &"fib" with (Val #n)) @ exampleEnv "fiba"; ⊤ {{ v, ⌜v = #(fib n)⌝ }}).
Proof.
  iStartProof.
  wp_pures.
  destruct (bool_decide _) eqn:Heq.
  - wp_pures. iModIntro. apply bool_decide_eq_true in Heq.
    assert (n=0 \/ n=1) as [-> | ->] by lia; done.
  - wp_pures. apply bool_decide_eq_false in Heq. wp_bind (FunCall _ _).
    assert ((n-1)%Z=(n-1)%nat) as -> by lia.
    iApply (wp_extern' _ "fiba" [ #((n-1)%nat)] _ _); first by (iPureIntro; vm_compute).
    do 3 iModIntro. cbn. rewrite Nat2Z.id.
    wp_pures.
    assert ((n-2)%Z=(n-2)%nat) as -> by lia. wp_bind (FunCall _ _).
    iApply (wp_extern' _ "fiba" [ #((n-2)%nat)] _ _); first by (iPureIntro; vm_compute).
    do 3 iModIntro. cbn. rewrite Nat2Z.id.
    wp_pures.
    iModIntro. iPureIntro. rewrite <- Nat2Z.inj_add.
    repeat f_equal.
    assert (n = S (S (n-2))) as -> by lia.
    cbn. do 2 f_equal. lia.
Qed.


Tactic Notation "wp_storee" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l I↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "I↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => idtac K e'; eapply (tac_wp_store _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [iSolveTC
    |solve_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.


Lemma heap_prog_correct (n:nat)
  : ⊢ (WP heap_example @ exampleEnv "fib"; ⊤ {{ v, ⌜v = #1337⌝ }}).
Proof.
  iStartProof. unfold heap_example.
  wp_alloc l as "Hl"; first lia. change (Z.to_nat 2) with 2. destruct l as [l]. cbn. unfold loc_add; cbn.
  iDestruct "Hl" as "(Hl0 & Hl1 & _)".
  wp_pures.
  wp_store.
  wp_pures.
  wp_store.
  wp_free.
  wp_pures.
  rewrite Z.add_0_r.
  wp_load.
  done.
Qed.

End examples.
