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

Definition fib_prog name (x:expr) := 
(if: "x" < #2 
 then "x"
 else (call: (&name) with ("x" - #1)) + (call: (&name) with ("x" - #2) ))%E.
Definition heap_example : expr :=
  let: "x" := malloc (#2) in 
 (call: &"store_it" with (("x" +ₗ #1), call: &"fib_impl" with ( Val (#3) )) ;;
 ("x" +ₗ #0) <- #1337 ;;
  let: "y" := *("x" +ₗ #1) in
  free ("x" +ₗ #1, #1) ;;
  *"x" + "y").

Definition fib_func name : function := Fun [BNamed "x"] (fib_prog name "x").
Definition exampleProgram name : gmap string function :=
  insert "fib_impl" (fib_func name) ∅.

Definition exampleEnv name : prog_environ := {|
  weakestpre.prog := exampleProgram name;
  T := λ s v Φ, match (s,v) with
      ("fib_axiom", [ #(LitInt z) ]) => (⌜(z >= 0)%Z⌝ ∗ Φ (#(fib (Z.to_nat z))))%I
    | ("store_it", [ #(LitLoc l) ; v' ]) => (∃ v, (l I↦ v) ∗ ((l ↦{DfracOwn 1} v') -∗ Φ (#0)))%I
    | _ => ⌜False⌝%I end
|}.


Definition exampleEnvAfterLinking name : prog_environ := {|
  weakestpre.prog := insert "fib_axiom" (fib_func "fib_impl") (exampleProgram name);
  T := λ s v Φ, match (s,v) with
    | ("store_it", [ #(LitLoc l) ; v' ]) => (∃ v, (l I↦ v) ∗ ((l ↦{DfracOwn 1} v') -∗ Φ (#0)))%I
    | _ => ⌜False⌝%I end
|}.

(* A simple recursive function *)
Lemma fib_prog_correct' (n:nat)
  : ⊢ (WPCall "fib_impl" with [ #n ] @ exampleEnv "fib_impl"; ⊤ {{ v, ⌜v = #(fib n)⌝ }}).
Proof.
  iStartProof.
  iLöb as "IH" forall (n).
  iApply prove_wp_call. 1-2: iPureIntro; reflexivity.
  wp_finish.
  wp_pures.
  destruct (bool_decide _) eqn:Heq.
  - wp_pures. iModIntro. apply bool_decide_eq_true in Heq.
    assert (n=0 \/ n=1) as [-> | ->] by lia; done.
  - do 2 wp_pure _. apply bool_decide_eq_false in Heq. wp_bind (FunCall _ _).
    wp_apply wp_wand.
    { assert ((n-1)%Z=(n-1)%nat) as -> by lia. wp_call. iApply "IH". }
    iIntros (v) "->". wp_bind (FunCall _ _). wp_pure _. wp_apply wp_wand.
    { assert ((n-2)%Z=(n-2)%nat) as -> by lia. wp_call. iApply "IH". }
    iIntros (v) "->". wp_pures. iModIntro. iPureIntro. rewrite <- Nat2Z.inj_add.
    repeat f_equal.
    assert (n = S (S (n-2))) as -> by lia.
    cbn. do 2 f_equal. lia.
Qed.

Lemma fib_prog_correct (n:nat)
  : ⊢ (WP (call: &"fib_impl" with (Val #n)) @ exampleEnv "fib_impl"; ⊤ {{ v, ⌜v = #(fib n)⌝ }}).
Proof.
  iStartProof.
  wp_call. iApply fib_prog_correct'.
Qed.

(* A call to an axiomatically specified function *)
Lemma fiba_prog_correct' (n:nat)
  : ⊢ (WPFun (fib_func "fib_axiom") with [ #n ] @ exampleEnv "fib_axiom"; ⊤ {{ v, ⌜v = #(fib n)⌝ }}).
Proof.
  iStartProof.
  iApply prove_wp_fun'. 1: iPureIntro; reflexivity. do 3 iModIntro.
  wp_pures.
  destruct (bool_decide _) eqn:Heq.
  - wp_pures. iModIntro. apply bool_decide_eq_true in Heq.
    assert (n=0 \/ n=1) as [-> | ->] by lia; done.
  - wp_pures. apply bool_decide_eq_false in Heq. wp_extern.
    assert ((n-1)%Z=(n-1)%nat) as -> by lia.
    cbn. iModIntro. rewrite Nat2Z.id. iSplitR; first (iPureIntro; cbn; lia).
    wp_pures.
    assert ((n-2)%Z=(n-2)%nat) as -> by lia. wp_extern.
    iModIntro. cbn. rewrite Nat2Z.id. iSplitR; first (iPureIntro; cbn; lia).
    wp_pures.
    iModIntro. iPureIntro. rewrite <- Nat2Z.inj_add.
    repeat f_equal.
    assert (n = S (S (n-2))) as -> by lia.
    cbn. do 2 f_equal. lia.
Qed.

Lemma fiba_prog_correct (n:nat)
  : ⊢ (WP (call: &"fib_impl" with (Val #n)) @ exampleEnv "fib_axiom"; ⊤ {{ v, ⌜v = #(fib n)⌝ }}).
Proof.
  iStartProof.
  wp_call. iApply prove_wp_call_wp_fun; first done. iApply fiba_prog_correct'.
Qed.

(* Calling the function calling the axiomatically specified function *)

Lemma fib_impl_axiom_prog_correct' (n:nat)
  : ⊢ (WPFun (fib_func "fib_impl") with [ #n ] @ exampleEnv "fib_axiom"; ⊤ {{ v, ⌜v = #(fib n)⌝ }}).
Proof.
  iStartProof.
  iApply prove_wp_fun'. 1: iPureIntro; reflexivity. do 3 iModIntro.
  wp_pures.
  destruct (bool_decide _) eqn:Heq.
  - wp_pures. iModIntro. apply bool_decide_eq_true in Heq.
    assert (n=0 \/ n=1) as [-> | ->] by lia; done.
  - do 2 wp_pure _. apply bool_decide_eq_false in Heq. wp_bind (FunCall _ _).
    wp_apply wp_wand.
    { assert ((n-1)%Z=(n-1)%nat) as -> by lia. iApply fiba_prog_correct. }
    iIntros (v) "->". wp_bind (FunCall _ _). wp_pure _. wp_apply wp_wand.
    { assert ((n-2)%Z=(n-2)%nat) as -> by lia. iApply fiba_prog_correct. }
    iIntros (v) "->". wp_pures. iModIntro. iPureIntro. rewrite <- Nat2Z.inj_add.
    repeat f_equal.
    assert (n = S (S (n-2))) as -> by lia.
    cbn. do 2 f_equal. lia.
Qed.

Lemma heap_prog_correct (n:nat)
  : ⊢ (WP heap_example @ exampleEnv "fib_impl"; ⊤ {{ v, ⌜v = #(1337 + fib 3)⌝ }}).
Proof.
  iStartProof. unfold heap_example.
  wp_alloc l as "Hl"; first lia. change (Z.to_nat 2) with 2.
  destruct l as [l]. cbn. unfold loc_add; cbn.
  iDestruct "Hl" as "(Hl0 & Hl1 & _)".
  do 2 wp_pure _.
  wp_bind (FunCall _ _).
  wp_apply wp_wand. 1: change 3 with (Z.of_nat 3). 1: iApply (fib_prog_correct 3).
  iIntros (v) "->". wp_extern.
  iModIntro. cbn. iExists _. iFrame. iIntros "Hl1".
  wp_pures.
  wp_store.
  wp_pures.
  wp_load.
  wp_pures.
  wp_free.
  wp_pures.
  rewrite Z.add_0_r.
  wp_load.
  wp_pures.
  done.
Qed.

Section linking.

  (* This section is very ugly *)
  (* Ugly tactic to reduce matches on strings *)
  Ltac string_resolve s := 
      let b1 := fresh "b1" in
      let b2 := fresh "b2" in
      let b3 := fresh "b3" in
      let b4 := fresh "b4" in
      let b5 := fresh "b5" in
      let b6 := fresh "b6" in
      let b7 := fresh "b7" in
      let b8 := fresh "b8" in
      repeat (destruct s as [|[b1 b2 b3 b4 b5 b6 b7 b8] s]; try congruence; eauto;
                    destruct b1; try congruence; eauto;
                    destruct b2; try congruence; eauto;
                    destruct b3; try congruence; eauto;
                    destruct b4; try congruence; eauto;
                    destruct b5; try congruence; eauto;
                    destruct b6; try congruence; eauto;
                    destruct b7; try congruence; eauto;
                    destruct b8; try congruence; eauto). 

  (* Lemma using the "recursive link" lemma.
     Now fib recursively calls fiba, 
     and fiba recursively calls fib,
     so we do mutual recursion, whereas previously,
     recursive calls terminated in external functions *)
  Lemma fiba_correct_link_rec (n:nat)
    : ⊢ (WP (call: &"fib_impl" with (Val #n)) @ exampleEnvAfterLinking "fib_axiom"; ⊤ {{ v, ⌜v = #(fib n)⌝ }}).
  Proof.
    iStartProof.
    iApply (wp_link_rec (exampleEnv "fib_axiom") _ _ "fib_axiom").
    2: iPureIntro; cbn; reflexivity.
    1: iPureIntro; cbn; unfold exampleEnv, exampleProgram; set_solver.
    - iIntros "!> %s %vv %Ψ [%Hdom %Hne] HT".
      unfold exampleEnv, exampleEnvAfterLinking; cbn.
      string_resolve s. (* <- Takes some time *)
    - (* We now need to show that the successor state of the function call we are replacing,
         within the old/smaller context. We have already proven this.  *)
      iIntros "!> %vv %Ψ HT". destruct vv as [|[[]] []]; cbn -[apply_func]; eauto.
      iDestruct "HT" as "(%HTL & HT)". clear n. assert (exists n:nat, Z.of_nat n = n0) as (n & <-).
      1: exists (Z.to_nat n0); lia.
      iApply wp_wand_fun; first iApply fib_impl_axiom_prog_correct'.
      iIntros (v) "->". rewrite Nat2Z.id. done.
    - iApply fiba_prog_correct.
  Qed.

  (* We now do the same with the other linking lemma, where we must show that the implementation of
     the function we are replacing is correct, and not the "successor state after function invokation".
     The flipside is that we have to do this proof in the new environment. 

     In that environment, fib and fiba are mutually recursive, so we have to redo the entire correctness proof.
     Since they share the same source code, the proof is the same for both. *)
  Lemma fiba_prog_correct_for_link (n:nat)
    : ⊢ ((WP (call: &"fib_impl" with (Val #n)) @ exampleEnvAfterLinking "fib_axiom"; ⊤ {{ v, ⌜v = #(fib n)⌝ }}) ∗
         WP (call: &"fib_axiom" with (Val #n)) @ exampleEnvAfterLinking "fib_axiom"; ⊤ {{ v, ⌜v = #(fib n)⌝ }}).
  Proof.
    iStartProof.
    iLöb as "IH" forall (n). iSplitL.
    all: wp_pures.
    all: destruct (bool_decide _) eqn:Heq.
    1,3: wp_pures; iModIntro; apply bool_decide_eq_true in Heq.
    1,2:  assert (n=0 \/ n=1) as [-> | ->] by lia; done.
    all: do 2 wp_pure _; apply bool_decide_eq_false in Heq; wp_bind (FunCall _ _).
    all: wp_apply wp_wand.
    1,3: assert ((n-1)%Z=(n-1)%nat) as -> by lia.
    1,2: iDestruct ("IH" $! _) as "(IH1 & IH2)". 1: iApply "IH2". 1: iApply "IH1".
    all: iIntros (v) "->"; wp_bind (FunCall _ _); wp_pure _; wp_apply wp_wand.
    1,3: assert ((n-2)%Z=(n-2)%nat) as -> by lia.
    1,2: iDestruct ("IH" $! _) as "(IH1 & IH2)". 1: iApply "IH2". 1: iApply "IH1".
    all: iIntros (v) "->"; wp_pures; iModIntro; iPureIntro; rewrite <- Nat2Z.inj_add.
    all: repeat f_equal.
    all: assert (n = S (S (n-2))) as -> by lia.
    all: cbn; do 2 f_equal; lia.
  Qed.

  (* we can now use this result above to prove the linking. Note that we have not actually gained anything,
     our linking proof presupposes a proof that the entire program is correct all on its own *)

  Lemma fiba_correct_link (n:nat)
    : ⊢ (WP (call: &"fib_impl" with (Val #n)) @ exampleEnvAfterLinking "fib_axiom"; ⊤ {{ v, ⌜v = #(fib n)⌝ }}).
  Proof.
    iStartProof.
    iApply (wp_link (exampleEnv "fib_axiom") _ _ "fib_axiom").
    2: iPureIntro; cbn; reflexivity.
    1: iPureIntro; cbn; unfold exampleEnv, exampleProgram; set_solver.
    - iIntros "!> %s %vv %Ψ [%Hdom %Hne] HT".
      unfold exampleEnv, exampleEnvAfterLinking; cbn.
      string_resolve s.
    - iIntros "!> %vv %Ψ HT"; destruct vv as [|[[]] []]; cbn; eauto.
      iDestruct "HT" as "(%HTL & HT)". clear n. assert (exists n:nat, Z.of_nat n = n0) as (n & <-).
      1: exists (Z.to_nat n0); lia.
      wp_apply wp_wand.
      {iDestruct (fiba_prog_correct_for_link _) as "(H1 & H2)". iApply "H2". }
      iIntros (v) "->". by rewrite Nat2Z.id.
    - iApply fiba_prog_correct.
  Qed.


End linking.


End examples.
