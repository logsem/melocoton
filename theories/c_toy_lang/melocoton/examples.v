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
  wp_pure _.
  iLöb as "IH" forall (n).
  wp_pure _.
  destruct (bool_decide _) eqn:Heq.
  - wp_pure _. iModIntro. apply bool_decide_eq_true in Heq.
    assert (n=0 \/ n=1) as [-> | ->] by lia; done.
  - wp_pure _. apply bool_decide_eq_false in Heq. wp_bind (FunCall _ _).
    wp_pure _. wp_apply wp_wand.
    { assert ((n-1)%Z=(n-1)%nat) as -> by lia. wp_pure _. iApply "IH". }
    iIntros (v) "->". wp_bind (FunCall _ _). wp_pure _. wp_apply wp_wand.
    { assert ((n-2)%Z=(n-2)%nat) as -> by lia.  wp_pure _. iApply "IH". }
    iIntros (v) "->". wp_pure _. iModIntro. iPureIntro. rewrite <- Nat2Z.inj_add.
    repeat f_equal.
    assert (n = S (S (n-2))) as -> by lia.
    cbn. do 2 f_equal. lia.
Qed.

(* A call to an axiomatically specified function *)


Lemma fiba_prog_correct (n:nat)
  : ⊢ (WP (call: &"fib" with (Val #n)) @ exampleEnv "fiba"; ⊤ {{ v, ⌜v = #(fib n)⌝ }}).
Proof.
  iStartProof.
  wp_pure _.
  wp_pure _.
  destruct (bool_decide _) eqn:Heq.
  - wp_pure _. iModIntro. apply bool_decide_eq_true in Heq.
    assert (n=0 \/ n=1) as [-> | ->] by lia; done.
  - wp_pure _. apply bool_decide_eq_false in Heq. wp_bind (FunCall _ _).
    wp_pure _.
    assert ((n-1)%Z=(n-1)%nat) as -> by lia.
    iApply (wp_extern' _ "fiba" [ #((n-1)%nat)] _ _); first by (iPureIntro; vm_compute).
    do 3 iModIntro. cbn. rewrite Nat2Z.id.
    wp_pure _.
    assert ((n-2)%Z=(n-2)%nat) as -> by lia. wp_bind (FunCall _ _).
    iApply (wp_extern' _ "fiba" [ #((n-2)%nat)] _ _); first by (iPureIntro; vm_compute).
    do 3 iModIntro. cbn. rewrite Nat2Z.id.
    wp_pures.
    iModIntro. iPureIntro. rewrite <- Nat2Z.inj_add.
    repeat f_equal.
    assert (n = S (S (n-2))) as -> by lia.
    cbn. do 2 f_equal. lia.
Qed.

End examples.
