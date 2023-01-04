From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From melocoton.ml_toy_lang Require Import lang notation melocoton.proofmode.
From melocoton.language Require Import language wp_link.
From iris.prelude Require Import options.
Import uPred.


(** Heap tactics *)
Section examples.

Context `{!heapGS_ML Σ, !invGS_gen hlc Σ}.

Definition call_inc : expr ML_lang := 
  let: "l" := ref (#0 + #0)
  in "l" <- #41 ;; Extern "inc" [Var "l"];; ! "l".

Definition IncrementSpec := λ s v Φ, match (s,v) with
      ("inc", [ #(LitLoc l) ]) => (∃ (z:Z), (l ↦M #z) ∗ ((l ↦M #(z+1)) -∗ Φ #()))%I
    | _ => ⌜False⌝%I end.

Definition inc_impl : expr ML_lang := let: "k" := ! "l" + #1 in "l" <- "k";; #().
Definition inc_func := MlFun [BNamed "l"] inc_impl.

Definition AxiomEnv : prog_environ ML_lang Σ := {|
  penv_prog := ∅;
  penv_proto := IncrementSpec;
|}.

Lemma prog_correct
 : ⊢ (WP call_inc @ AxiomEnv ; ⊤ {{v, ⌜v = #42⌝}})%I.
Proof.
  iStartProof. unfold call_inc.
  wp_pures. unfold Z.add.
  wp_alloc l as "Hl". wp_pures.
  wp_store. wp_extern.
  iModIntro. cbn. iExists 41%Z. iFrame. iIntros "Hl".
  wp_pures. wp_load. iModIntro. done.
Qed.

Definition EmptySpec : (string -d> list val -d> (val -d> iPropO Σ) -d> iPropO Σ) := λ _ _ _, ⌜False⌝%I.

Definition SpecifiedEnv : prog_environ ML_lang Σ := {|
  penv_prog := <[ "inc" := inc_func ]> ∅;
  penv_proto := EmptySpec;
|}.

Lemma inc_correct l (z:Z)
 : ⊢ l ↦M #z -∗ (WP Extern "inc" [ Val #l ] @ SpecifiedEnv ; ⊤ {{v, l ↦M #(z+1) ∗ ⌜v = #()⌝}})%I.
Proof.
  iStartProof. iIntros "Hz". wp_call. iApply prove_wp_call; [done|done|]. wp_finish.
  wp_load. wp_pures. wp_store. iModIntro. iSplitL; done.
Qed.

Lemma left_correct : ⊢ env_fulfills AxiomEnv EmptySpec.
Proof.
  iStartProof. iIntros (s vv Φ []).
Qed.

Ltac string_resolve s t := 
    let b1 := fresh "b1" in
    let b2 := fresh "b2" in
    let b3 := fresh "b3" in
    let b4 := fresh "b4" in
    let b5 := fresh "b5" in
    let b6 := fresh "b6" in
    let b7 := fresh "b7" in
    let b8 := fresh "b8" in
    repeat (destruct s as [|[b1 b2 b3 b4 b5 b6 b7 b8] s]; (try t); eauto;
                  try (destruct b1; try t; eauto;
                  try (destruct b2; try t; eauto;
                  try (destruct b3; try t; eauto;
                  try (destruct b4; try t; eauto;
                  try (destruct b5; try t; eauto;
                  try (destruct b6; try t; eauto;
                  try (destruct b7; try t; eauto;
                  try (destruct b8; try t; eauto))))))))). 

Ltac ft := (iDestruct "Hvv" as "%Hvv"; exfalso; done).
Lemma right_correct : ⊢ env_fulfills SpecifiedEnv IncrementSpec.
Proof.
  iStartProof. iIntros (s vv Φ) "Hvv". unfold IncrementSpec.
  string_resolve s ft.
  destruct vv as [ | [[l| | | |]| | | |] [|[[z| | | |]| | | |] []]]; try ft.
  iSplitR; first done. cbn.
  iDestruct "Hvv" as "(%z & Hz & Hres)".
  wp_apply (wp_wand with "[Hz] [Hres]").
  + wp_apply (inc_correct with "Hz").
  + iIntros (v) "(Hv & ->)". iApply ("Hres" with "Hv").
Qed.


Instance example_can_link : can_link EmptySpec IncrementSpec EmptySpec IncrementSpec
         ∅ (<[ "inc" := inc_func ]> ∅) (<[ "inc" := inc_func ]> ∅).
Proof. split.
  - set_solver.
  - iIntros (s vv Φ) "Hvv". iRight. done.
  - iIntros (s vv Φ) "[]".
  - iIntros (s vv Φ) "[]".
  - iIntros (s vv Φ) "Hvv".
    iDestruct (right_correct $! s vv Φ with "Hvv") as "[$ HR]".
    iApply wp_pe_mono. 2: iApply "HR". split; try easy. cbn.
    iIntros (? ? ?) "? []".
  - cbn. apply map_eq_iff. intros i. destruct (decide (i = "inc")); set_solver.
Qed.

Lemma link_executions
 : ⊢ (WP call_inc @ SpecifiedEnv ; ⊤ {{v, ⌜v = #42⌝}})%I.
Proof.
  iApply (wp_link_execs _ _ _ _ _ $! _ _ 0).
  cbn. iApply wp_pe_mono. 2: iApply prog_correct.
  split; try reflexivity. 
  iIntros (s vv Φ) "%Hdom Hvv". cbn -[IncrementSpec].
  iLeft. iExists 1. cbn [nth_error]. iSplitR; done.
Qed.

End examples.
