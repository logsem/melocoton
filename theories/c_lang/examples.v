From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From melocoton.language Require Import wp_link.
From iris.proofmode Require Export tactics.
From melocoton.c_lang Require Import lang notation proofmode.
From iris.prelude Require Import options.
Import uPred.


(** Heap tactics *)
Section examples.
Context `{SI:indexT}.
Context `{!heapG_C Σ, !invG Σ}.
 
Fixpoint fib (n:nat) : nat := match n with
  0 => 0
| S n' => match n' with 
      0 => 1
    | S n'' => fib n' + fib n'' end end.

Definition fib_prog name (x:expr) : expr :=
(if: "x" < #2 
 then "x"
 else (call: (&name) with ("x" - #1)) + (call: (&name) with ("x" - #2) )).

Definition heap_example : expr :=
  let: "x" := malloc (#2) in 
 (call: &"store_it" with (("x" +ₗ #1), call: &"fib_left" with ( Val (#3) )) ;;
 ("x" +ₗ #0) <- #1337 ;;
  let: "y" := *("x" +ₗ #1) in
  free ("x" +ₗ #1, #1) ;;
  *"x" + "y").

Definition fib_func name : function := Fun [BNamed "x"] (fib_prog name "x").
Definition exampleProgram fname cname : gmap string function :=
  {[ fname := fib_func cname ]}.




Definition FibSpec name := (λ (s:string) (v:list val) (Φ : (val → iPropI Σ)),
  ⌜s = name⌝ ∗ ∃ z, ⌜v = [ #(LitInt z) ] ∧ (z >= 0)%Z⌝ ∗ Φ (#(fib (Z.to_nat z))))%I.

Definition StoreItSpec := (λ s v Φ,
  ⌜s = "store_it"⌝ ∗ ∃ l v', ⌜v = [ #(LitLoc l) ; v' ]⌝ ∗
  (∃ v, (l I↦C v) ∗ ((l ↦C v') -∗ Φ (#0))))%I.

Definition FibLeftSpec := FibSpec "fib_left".
Definition FibRightSpec := FibSpec "fib_right".

Definition SimpleEnv : prog_environ C_lang Σ :=
  ⟨ exampleProgram "fib_impl" "fib_impl", StoreItSpec ⟩.

Definition FinalSpec := (FibLeftSpec) ⊔ FibRightSpec.


Definition LeftEnv : prog_environ C_lang Σ :=
  ⟨ exampleProgram "fib_left" "fib_right", (* function called fib_left calls fib_right *)
    FibRightSpec ⊔ StoreItSpec ⟩.

Definition RightEnv : prog_environ C_lang Σ :=
  ⟨ exampleProgram "fib_right" "fib_left", (* function called fib_right calls fib_left *)
    FibLeftSpec ⊔ StoreItSpec ⟩.

Definition FinalEnv : prog_environ C_lang Σ :=
  ⟨ {[ "fib_right" := fib_func "fib_left"; "fib_left" := fib_func "fib_right" ]},
    StoreItSpec ⟩.

(* A simple recursive function *)
Lemma fib_prog_correct' (n:nat)
  : ⊢ (WP (call: &"fib_impl" with (Val #n)) @ SimpleEnv; ⊤ {{ v, ⌜v = #(fib n)⌝ }})%CE.
Proof.
  iStartProof.
  iLöb as "IH" forall (n).
  wp_pures.
  destruct (bool_decide _) eqn:Heq.
  - wp_pures. iModIntro. apply bool_decide_eq_true in Heq.
    assert (n=0 ∨ n=1) as [-> | ->] by lia; done.
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

Lemma heap_prog_correct (n:nat)
  : ⊢ (WP heap_example @ RightEnv; ⊤ {{ v, ⌜v = #(1337 + fib 3)⌝ }}).
Proof.
  iStartProof. unfold heap_example.
  wp_alloc l as "Hl"; first lia. change (Z.to_nat 2) with 2.
  destruct l as [l]. cbn. unfold loc_add; cbn.
  iDestruct "Hl" as "(Hl0 & Hl1 & _)".
  do 2 wp_pure _.
  change (l + 1)%Z with (l + 1%nat)%Z.
  wp_bind (FunCall _ _).
  change 3 with (Z.of_nat 3).
  wp_extern. cbn. iLeft. cbn. iModIntro.
  iSplit; first done. iExists _; iSplit; first done.
  wp_pures.
  wp_bind (FunCall _ _).
  wp_extern. cbn. iRight. cbn. iModIntro.
  iSplit; first done. iExists _, _. iSplit; first done.
  iExists _. iFrame. iIntros "Hl1".
  wp_pures.
  wp_pures.
  wp_apply (wp_store with "Hl0"); iIntros "Hl0".
  wp_pures.
  wp_apply (wp_load with "Hl1"); iIntros "Hl1".
  wp_pures.
  wp_free.
  wp_pures.
  rewrite Z.add_0_r.
  wp_apply (wp_load with "Hl0"); iIntros "Hl0".
  wp_pures.
  done.
Qed.

Section linking.

Lemma fib_left_correct :
  (FibRightSpec ⊔ StoreItSpec) ||- exampleProgram "fib_left" "fib_right" :: FibLeftSpec.
Proof.
  apply prove_prog_correct.
  { iIntros (? ? ?) "[%H [% _]]". set_solver. }
  iIntros (s vv Φ Φ') "H Hcont". unfold FibLeftSpec.
  iDestruct "H" as "(-> & H)". iDestruct "H" as (? (-> & ?)) "H".
  assert (exists n, Z.of_nat n = z) as [n <-].
  1: {exists (Z.to_nat z). lia. }
  wp_pures.
  destruct (bool_decide _) eqn:Heq.
  - wp_pures. iModIntro. apply bool_decide_eq_true in Heq.
    assert (n=0 \/ n=1) as [-> | ->] by lia; by iApply "Hcont".
  - do 2 wp_pure _. apply bool_decide_eq_false in Heq. wp_bind (FunCall _ _).
    wp_extern. cbn. iLeft. cbn. iModIntro. iSplit; first done.
    iExists _. iSplit. { iPureIntro. split; eauto; lia. }
    wp_pures. wp_bind (FunCall _ _). wp_pures.
    wp_extern. cbn. iLeft. cbn. iModIntro.
    iSplit; first done. iExists _. iSplit. { iPureIntro; split; eauto; lia. }
    wp_pures. wp_pures. iModIntro.
    assert (Z.to_nat (n - 1) = Z.to_nat n - 1) as -> by lia.
    assert (Z.to_nat (n - 2) = Z.to_nat n - 2) as -> by lia.
    rewrite ! Nat2Z.id.
    assert (exists n', n = S(S(n'))) as [n' ->].
    {destruct n as [|[|n']]; try lia. now exists n'. }
    cbn -[fib]. rewrite Nat.sub_0_r. rewrite <- Nat2Z.inj_add.
    by iApply "Hcont".
Qed.


Lemma fib_right_correct :
  (FibLeftSpec ⊔ StoreItSpec) ||- exampleProgram "fib_right" "fib_left" :: FibRightSpec.
Proof.
  apply prove_prog_correct.
  { iIntros (? ? ?) "[%H [% _]]". set_solver. }
  iIntros (s vv Φ Φ') "H Hcont". unfold FibLeftSpec.
  iDestruct "H" as "(-> & H)". iDestruct "H" as (? (-> & ?)) "H".
  assert (exists n, Z.of_nat n = z) as [n <-].
  1: {exists (Z.to_nat z). lia. }
  wp_pures.
  destruct (bool_decide _) eqn:Heq.
  - wp_pures. iModIntro. apply bool_decide_eq_true in Heq.
    assert (n=0 \/ n=1) as [-> | ->] by lia; by iApply "Hcont".
  - do 2 wp_pure _. apply bool_decide_eq_false in Heq. wp_bind (FunCall _ _).
    wp_extern. cbn. iLeft. cbn. iModIntro.
    iSplit; first done. iExists _. iSplit. { iPureIntro; split; eauto; lia. }
    wp_pures. wp_bind (FunCall _ _). wp_pures.
    wp_extern. cbn. iLeft. cbn. iModIntro.
    iSplit; first done. iExists _. iSplit. { iPureIntro; split; eauto; lia. }
    wp_pures. wp_pures. iModIntro.
    assert (Z.to_nat (n - 1) = Z.to_nat n - 1) as -> by lia.
    assert (Z.to_nat (n - 2) = Z.to_nat n - 2) as -> by lia.
    rewrite ! Nat2Z.id.
    assert (exists n', n = S(S(n'))) as [n' ->].
    {destruct n as [|[|n']]; try lia. now exists n'. }
    cbn -[fib]. rewrite Nat.sub_0_r. rewrite <- Nat2Z.inj_add.
    by iApply "Hcont".
Qed.

Lemma example_can_link : can_link FibLeftSpec FibRightSpec StoreItSpec (FibLeftSpec ⊔ FibRightSpec)
         (exampleProgram "fib_left" "fib_right") (exampleProgram "fib_right" "fib_left") (penv_prog FinalEnv).
Proof.
  assert (
    ((<["fib_right":=fib_func "fib_left"]> (<["fib_left":=fib_func "fib_right"]> ∅)))
  = (union_with (λ _ _ : func C_lang, None) (exampleProgram "fib_left" "fib_right") (exampleProgram "fib_right" "fib_left"))) as Heq.
  { apply map_eq_iff. intros i. 
    destruct (decide (i = "fib_right")) as [-> | Hno].
    1: done.
    destruct (decide (i = "fib_left")) as [-> | Hno2].
    1: done.
    rewrite lookup_union_with.
    rewrite ! lookup_insert_ne. 2-4: done. cbn. done. }
  split.
  - unfold exampleProgram. set_solver.
  - iIntros (s vv Φ) "Hvv". iApply "Hvv".
  - iIntros (s vv Φ) "[-> H]". done.
  - apply fib_left_correct.
  - apply fib_right_correct.
  - unfold FinalEnv. cbn. rewrite Heq. done.
Qed.

Lemma fib_link_correct :
  StoreItSpec ||- {[ "fib_right" := fib_func "fib_left"; "fib_left" := fib_func "fib_right" ]} :: FinalSpec.
Proof.
  eapply wp_link_progs, can_link_can_link_all, example_can_link.
Qed.

End linking.

End examples.
