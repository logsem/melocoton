From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From melocoton.combined Require Import adequacy.
From melocoton.ml_lang Require Import lang notation proofmode.
From melocoton.language Require Import language wp_link.
From melocoton.language Require Import language wp_link.
From iris.prelude Require Import options.
From transfinite.base_logic.lib Require Import satisfiable invariants.
From melocoton.lang_to_mlang Require Import backwards_adequacy.
Import uPred.


(** Heap tactics *)
Section examples.
Context `{SI:indexT}.

Context `{!heapG_ML Σ, !invG Σ}.

Definition call_inc : ML_lang.expr :=
  let: "l" := ref (#0 + #0)
  in "l" <- #41 ;; Extern "inc" [Var "l"];; ! "l".

Definition IncrementSpec := (λ s v Φ,
  ⌜s = "inc"⌝ ∗ ∃ l, ⌜v = [ #(LitLoc l) ]⌝ ∗
  ∃ (z:Z), (l ↦M #z) ∗ ((l ↦M #(z+1)) -∗ Φ (OVal #())))%I.

Definition inc_impl (l : ML_lang.expr) : ML_lang.expr := let: "k" := ! l + #1 in l <- "k";; #().
Definition inc_func := MlFun [BNamed "l"] (inc_impl "l").

Definition AxiomEnv : prog_environ ML_lang Σ :=
  ⟨ ∅, IncrementSpec ⟩.

Lemma prog_correct
 : ⊢ (WP call_inc at AxiomEnv {{v, ⌜v = OVal #42⌝}})%I.
Proof.
  iStartProof. unfold call_inc.
  wp_pures. unfold Z.add.
  wp_apply (wp_alloc with "[//]"); iIntros (l) "[Hl _]".
  wp_pures.
  wp_apply (wp_store with "Hl"); iIntros "Hl". wp_pures.
  wp_extern.
  iModIntro. cbn. iSplit; first done. iExists _; iSplit; first done.
  iExists 41%Z. iFrame. iIntros "Hl".
  wp_pures.
  wp_apply (wp_load with "Hl"); iIntros "Hl".
  done.
Qed.

Definition SpecifiedEnv : prog_environ ML_lang Σ :=
  ⟨ {[ "inc" := inc_func ]}, ⊥ ⟩.

Lemma inc_correct l (z:Z)
 : ⊢ l ↦M #z -∗ WP inc_impl (#l) at SpecifiedEnv {{v, l ↦M #(z+1) ∗ ⌜v = OVal #()⌝}}%I.
Proof.
  iStartProof. iIntros "Hz". unfold inc_impl.
  wp_pures.
  wp_apply (wp_load with "Hz"); iIntros "Hz".
  wp_pures.
  wp_apply (wp_store with "Hz"); iIntros "Hz".
  wp_pures.
  iModIntro. iSplitL; done.
Qed.

Lemma left_correct : IncrementSpec ||- ∅ :: ⊥.
Proof.
  iStartProof. iIntros (s vv Φ []).
Qed.

Lemma right_correct : ||- {[ "inc" := inc_func ]} :: IncrementSpec.
Proof.
  intros Ψ. apply prove_prog_correct.
  { iIntros (? ? ?) "[% [% ?]]". set_solver. }
  iIntros (s vv Φ Φ') "Hvv Hcont". unfold IncrementSpec.
  iDestruct "Hvv" as "(-> & H)". iDestruct "H" as (? -> ?) "[Hz Hres]".
  iApply wp_call; [done..|]. iNext.
  iApply (wp_wand with "[Hz] [Hres Hcont]").
  + iApply wp_proto_mono. 2: iApply (inc_correct with "Hz").
    apply proto_refines_bot_l.
  + iIntros (v) "(Hv & ->)". iApply "Hcont". iApply ("Hres" with "Hv").
Qed.

Instance example_can_link : can_link ⊥ IncrementSpec ⊥ IncrementSpec
         ∅ ({[ "inc" := inc_func ]}) ({[ "inc" := inc_func ]}).
Proof. split.
  - set_solver.
  - iIntros (s vv Φ) "Hvv". iRight. done.
  - iIntros (s vv Φ) "[]".
  - iIntros (s vv Φ) "[]".
  - iIntros (s vv Φ) "Hvv".
    by iApply right_correct.
  - cbn. apply map_eq_iff. intros i. destruct (decide (i = "inc")); set_solver.
Qed.

Lemma link_executions
 : ⊢ (WP call_inc at SpecifiedEnv {{v, ⌜v = OVal #42⌝}})%I.
Proof.
  iApply (wp_link_execs _ _ _ _ _ $! _ _ 0).
  cbn. iApply wp_proto_mono. 2: iApply prog_correct.
  iIntros (s vv Φ) "Hvv". cbn -[IncrementSpec].
  iLeft. iExists 1. cbn [nth_error]. iSplitR; done.
Qed.

Definition try_val : ML_lang.expr :=
  try: #1 + #1 with: "_" => #1.

Implicit Types Φ : outcome val → iProp Σ.

Lemma try_val_proof
 : ⊢ (WP try_val at AxiomEnv {{v, ⌜v = OVal #2⌝}})%I.
Proof.
  iStartProof. unfold try_val.
  wp_pures. unfold Z.add. cbn.
  wp_apply wp_try. wp_pures; eauto.
Qed.

Definition try_raise : ML_lang.expr :=
  try: (raise: #1 + #1) ;; #1 with: "v" => #1 + "v".



Ltac wp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         wp_bind_core K; tac_suc H)
     | _ => fail 1 "wp_apply: not a 'wp'"
     end)
  |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "wp_apply: cannot apply" lem ":" P ].

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => fail).


Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
    idtac K e';
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ K e');
      [tc_solve                       (* PureExec *)
      |try solve_vals_compare_safe; try eauto (* The pure condition for PureExec --
            handles trivial goals, including [vals_compare_safe] *)
      |tc_solve                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Lemma try_raise_proof
 : ⊢ (WP try_raise at AxiomEnv {{v, ⌜v = OVal #3⌝}})%I.
Proof.
  iStartProof. unfold try_raise. wp_pures.
  (* Set Printing Coercions. *)
  wp_apply (wp_try).
  wp_apply (wp_raise).
  wp_bind (Raise _).
  (* Unset Printing Notations. *)
  iApply wp_raise.
  Fail wp_pure (Rec BAnon BAnon _). wp_lam.
lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
        lazymatch K with | [] => fail 
        | _ => wp_bind_core K; idtac K e' end)
     | _ => fail 1 "wp_apply: not a 'wp'"
     end.

     wp_seq.
  wp_lam. wp_pures; eauto.
Qed.

End examples.

Section adequacy.
  Existing Instance ordinals.ordI.
  Local Definition e := call_inc.
  Local Definition σ : state ML_lang := ∅.
  Local Definition p : lang_prog ML_lang := {[ "inc" := inc_func ]}.
  Local Definition Φpure (σ : state ML_lang) v := v = OVal #42.

  Definition exampleΣ {SI: indexT} : gFunctors :=
    #[invΣ; heapΣ_ML].
  Global Instance subG_exampleΣ_invPreG `{SI: indexT} Σ :
    subG exampleΣ Σ → invPreG Σ.
  Proof. solve_inG. Qed.

  Global Instance subG_heapGpre_ML `{SI: indexT} Σ :
    subG ffiΣ Σ → heapGpre_ML Σ.
  Proof. solve_inG. Qed.


  Lemma example_adequacy e' σ' :
    rtc_step p e σ e' σ' → safe p e' σ' (Φpure σ').
  Proof.
    eapply (@mlang_to_lang_adequacy _ ML_lang exampleΣ).
    1: apply _.
    intros HinvG.
    intros P _ Halloc.
    unshelve eapply alloc_heapG_ML in Halloc as (HML&Halloc); last done.
    exists heapG_langG_ML.
    eapply alloc_mono; last exact Halloc.
    iIntros "($&$)".
    iSplit; last iApply link_executions.
    iSplit.
    - iIntros "!> %σ %v (Hσ&->) //".
    - iIntros "!> %F %s %vv []".
  Qed.

End adequacy.
