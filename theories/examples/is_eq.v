From transfinite.base_logic.lib Require Import na_invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils prims_proto.
From melocoton.language Require Import weakestpre progenv.
From melocoton.c_interop Require Import rules notation.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.ml_lang.logrel Require Import persistent_pred typing.
From melocoton.ml_lang.logrel Require logrel fundamental.
From melocoton.c_lang Require Import notation proofmode derived_laws.

Fixpoint valid_is_eq_type (τ : type) : Prop :=
  match τ with
  | TUnit | TNat | TBool => True
  | TArray τ => valid_is_eq_type τ
  | TProd τ1 τ2 | TSum τ1 τ2 => valid_is_eq_type τ1 ∧ valid_is_eq_type τ2
  | TArrow _ _ | TRec _ | TVar _ | TForall _ | TExist _ => False
  end.

Definition is_eq_code (x_arg y_arg : expr) : C_lang.expr :=
  let: "bx" := call: &"isblock" with (x_arg) in
  let: "by" := call: &"isblock" with (y_arg) in
  let: "res" := (
    if: "bx" ≠ "by" then #false else
      if: ! "bx" then
        (call: &"val2int" with (x_arg)) = (call: &"val2int" with (y_arg))
      else
        (* TODO *)
        #false
   ) in
   call: &"int2val" with ("res").

Definition is_eq_prog : lang_prog C_lang :=
  {[ "is_eq" := Fun [BNamed "x_arg"; BNamed "y_arg"] (is_eq_code "x_arg" "y_arg") ]}.

Section C_specs.
  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.
  Context `{!logrel.logrelG Σ}.

  Notation "⟦ τ ⟧  x" := (logrel.interp x τ) (at level 10).

  (* Import melocoton.ml_lang.logrel.logrel. *)

  Definition is_eq_spec_ML : protocol ML_lang.val Σ :=
    λ s vv Φ,
    (∃ x y τ Δ p,
      "->" ∷ ⌜s = "is_eq"⌝
    ∗ "->" ∷ ⌜vv = [ x; y ]⌝
    ∗ "%Hτ" ∷ ⌜valid_is_eq_type τ⌝
    ∗ "Hτx" ∷ ⟦ τ ⟧ p Δ x
    ∗ "Hτy" ∷ ⟦ τ ⟧ p Δ y
    ∗ "Hcont" ∷ Φ (ML_lang.LitV (bool_decide (x = y))))%I.

  Lemma is_eq_correct Ψ :
    prims_proto ⊤ Ψ ||- is_eq_prog @ ⊤ :: wrap_proto is_eq_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    unfold progwp.
    destruct lvs as [|lvx [|lvy [|??]]]; try done.
    all: cbn; iDestruct "Hsim" as "(Hx&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(Hy&?)"; try done.
    destruct ws as [|wx [|wy [|??]]]; decompose_Forall.
    iExists _. iSplit; first done.
    iExists _. solve_lookup_fixed. iSplit; first done. iNext.
    rewrite -/(is_eq_code _ _).
    iDestruct "Hx" as "-#Hx". iDestruct "Hy" as "-#Hy".
    iLöb as "IH" forall (τ x lvx wx y lvy wy Hτ H1 H2).
    destruct τ => //=; unfold is_eq_code.
    - (* TUnit *)
      iDestruct "Hτx" as %->.
      iDestruct "Hτy" as %->.
      iDestruct "Hx" as %->.
      iDestruct "Hy" as %->.
      wp_apply (wp_isblock with "HGC"); [done..|].
      iIntros "HGC". wp_pures.
      wp_apply (wp_isblock with "HGC"); [done..|].
      iIntros "HGC". wp_pures.
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC".
      wp_apply (wp_val2int with "HGC"); [done..|].
      iIntros "HGC". wp_pures => /=.
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (w) "[HGC %]".
      iApply ("Cont" with "HGC Hcont [] [//]").
      done.
    - (* TNat *) admit.
    - (* TBool *) admit.
    - (* TProd *) admit.
    - (* TSum *) admit.
    - (* TArray *) admit.
  Admitted.

End C_specs.
