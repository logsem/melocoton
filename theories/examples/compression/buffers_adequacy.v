From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.linking Require Import lang weakestpre.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import basics basics_resources wp_simulation.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils prims_proto.
From melocoton.language Require Import weakestpre progenv.
From melocoton.c_interop Require Import rules notation.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.c_lang Require Import notation proofmode derived_laws.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.combined Require Import adequacy.
From melocoton.examples.compression Require Import buffers_proofs buffers_specs buffers_client.


Section FixpointSpec.
  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

  Definition buf_library_spec_ML E := fixpoint (buf_library_spec_ML_pre E).
  Lemma buf_library_spec_ML_unfold E s vv Φ :
   (buf_library_spec_ML E s vv Φ ⊣⊢ buf_library_spec_ML_pre E (buf_library_spec_ML E) s vv Φ)%I.
  Proof.
    exact (fixpoint_unfold (buf_library_spec_ML_pre E) s vv Φ).
  Qed.
  Lemma buf_library_spec_ML_sim E:
   (buf_library_spec_ML E ⊑ buf_library_spec_ML_pre E (buf_library_spec_ML E))%I.
  Proof.
    iIntros (s vv Φ) "H". by iApply buf_library_spec_ML_unfold.
  Qed.

  Lemma ML_client_applied_spec_fix E:
    {{{ True }}}
      ML_client_applied_code @ ML_client_env E (buf_library_spec_ML E) ; E
    {{{ x, RET #x ; ⌜x=1%Z⌝ }}}.
  Proof.
    apply ML_client_applied_spec.
  Qed.

End FixpointSpec.

Local Existing Instance ordinals.ordI.

Definition fullprog : mlang_prog combined_lang :=
  combined_prog ML_client_applied_code buf_lib_prog_total.

Lemma buffers_adequate :
  umrel.trace (mlanguage.prim_step fullprog) (LkCall "main" [], adequacy.σ_init)
    (λ '(e, σ), mlanguage.to_val e = Some (code_int 1)).
Proof.
  eapply umrel_upclosed.
  { eapply combined_adequacy_trace. intros Σ Hffi E. split_and!.
    3: apply ML_client_applied_spec_fix.
    3: { rewrite wrap_proto_mono. 1: apply buffer_library_correct.
         apply buf_library_spec_ML_pre_mono, buf_library_spec_ML_sim. }
    { iIntros (? Hn ?) "(% & H)". unfold prim_names in H.
      rewrite !dom_insert dom_empty /= in H.
      iDestruct "H" as "[[[[H|H]|H]|H]|H]".
      all: iNamed "H"; exfalso; cbn in H; set_solver. }
    { set_solver. } }
  { by intros [? ?] (? & ? & ->). }
Qed.