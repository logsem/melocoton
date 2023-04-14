From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props multirelations.
From melocoton.language Require Import language weakestpre.
From melocoton.interop Require Import basics basics_resources prims_proto.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import state lang weakestpre update_laws wp_utils wp_simulation.
From melocoton.ml_lang Require Import primitive_laws lang_instantiation logrel.logrel.
From melocoton.c_lang Require Import lang_instantiation mlang_instantiation.
From melocoton.mlanguage Require Import progenv.
From melocoton.mlanguage Require Import weakestpre mlanguage adequacy.
From melocoton.linking Require Import lang weakestpre.

Notation combined_lang := (link_lang wrap_lang C_mlang).
Notation combined_prog e p := (link_prog wrap_lang C_mlang (wrap_prog e) p).

Class ffiG `{SI: indexT} (Σ : gFunctors) : Set := FFIG {
  ffiG_invG :> invG Σ;
  ffiG_CG :> heapG_C Σ;
  ffiG_MLG :> heapG_ML Σ;
  ffiG_wrapperG :> wrapperG Σ;
  ffiG_linkG :> linkG Σ;
  ffiG_logrelG :> logrelG Σ;
}.

Section combined_rules.
Context {SI: indexT}.
Context `{!ffiG Σ}.

Lemma combined_embed_c (p : lang_prog C_lang) (Ψ Ψ' : protocol C_intf.val Σ) :
  Ψ ||- p :: Ψ' →
  Ψ |- (link_lift2 wrap_lang _ p) :: Ψ'.
Proof.
  intros H%lang_to_mlang_correct. by apply link_lift2_correct.
Qed.

Lemma combined_correct
  (* `{indexT} `{!ffiG Σ} *)
  (e : ML_lang.expr) (p : lang_prog C_lang)
  (* (Ψ : ∀ `{!ffiG Σ}, protocol ML_lang.val Σ) *)
  (Ψ : protocol ML_lang.val Σ)
  (Pret : Z → Prop) (P : iProp Σ)
:
  Ψ on prim_names ⊑ ⊥ →
  dom p ## prim_names →
  (⊢ P -∗ WP e at ⟨ ∅ , Ψ ⟩ {{ k, ⌜∃ x, k = (ML_lang.LitV (ML_lang.LitInt x)) ∧ Pret x⌝ }}) →
  prims_proto Ψ ||- p :: wrap_proto Ψ →
  ⊥ |- combined_prog e p :: main_proto Pret P.
Proof.
  intros.
  eapply prog_triple_mono_r; swap 1 2.
  1: eapply link_close_correct.
  { rewrite dom_wrap_prog. set_solver. }
  1: eapply prog_triple_mono; last by apply wrap_correct.
  1: reflexivity.
  1: reflexivity.
  1: eapply prog_triple_mono; last by apply lang_to_mlang_correct.
  2: reflexivity.
  1: by rewrite -proto_refines_join_l.
  by rewrite -proto_refines_join_l -proto_refines_join_r.
Qed.

End combined_rules.
