From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources basics_constructions.
From melocoton.interop Require Import lang weakestpre update_laws prims_proto.
From melocoton.language Require Import weakestpre progenv wp_link.
From melocoton.c_interop Require Import rules notation.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.c_lang Require Import notation proofmode derived_laws.
From melocoton.examples.compression Require Import buffers_specs buffers_laws buffers_code 
  compression_specs compression_proofs
  buffers_proof_alloc buffers_proof_update buffers_proof_free buffers_proofs_compr
  buffers_proof_get.


Section Proofs.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

  Definition buf_lib_prog_total : gmap _ _ := buf_lib_prog ∪ buffy_env.

  Lemma buffer_library_correct_pre Ψ :
    (buffy_library_spec ⊔ prims_proto Ψ) ||- buf_lib_prog :: wrap_proto (buf_library_spec_ML_pre Ψ).
  Proof.
    iIntros (s vv Φ) "H". iNamed "H".
    iDestruct "Hproto" as "[[[[[Hproto|Hproto]|Hproto]|Hproto]|Hproto]|Hproto]".
    - iApply progwp_mono; [done|eapply prims_proto_refines_combspec|].
      iApply buf_alloc_correct. do 4 iExists _. iFrameNamed.
    - iApply progwp_mono; [done|eapply prims_proto_refines_combspec|].
      iApply buf_upd_correct. do 4 iExists _. iFrameNamed.
    - iApply progwp_mono; [done|eapply prims_proto_refines_combspec|].
      iApply buf_free_correct. do 4 iExists _. iFrameNamed.
    - iApply wrap_compress_correct. do 4 iExists _. iFrameNamed.
    - iApply wrap_max_len_correct. do 4 iExists _. iFrameNamed.
    - iApply progwp_mono; [done|eapply prims_proto_refines_combspec|].
      iApply buf_get_correct. do 4 iExists _. iFrameNamed.
  Qed.

  Lemma buffer_library_correct Ψ :
    prims_proto Ψ ||- buf_lib_prog_total :: wrap_proto (buf_library_spec_ML_pre Ψ).
  Proof.
    eassert (can_link_all (prims_proto Ψ) (wrap_proto (buf_library_spec_ML_pre Ψ)) buf_lib_prog_total _) as Hlink.
    - eapply can_link_can_link_all.
      assert (buf_lib_prog ##ₘ buffy_env) as Hdisj.
      1: { apply map_disjoint_dom. rewrite /buffy_env /buf_lib_prog !dom_insert_L !dom_empty_L. set_solver. }
      econstructor.
      5: eapply buffer_library_correct_pre.
      4: eapply buffy_library_correct; done.
      1: by apply map_disjoint_dom.
      1: iIntros (s vv Φ) "H"; by iRight.
      1: { iIntros (s vv Φ) "H"; iNamed "H".
           cbn. rewrite !dom_union_L !dom_insert_L !dom_empty_L.
           destruct p; try (iNamed "H"; iPureIntro; set_solver). cbn. done. }
      eapply map_eq_iff. intros s.
      rewrite /buf_lib_prog_total map_union_comm. 2:done. rewrite lookup_union lookup_union_with.
      destruct (buffy_env !! s) eqn:Heq1; rewrite Heq1;
      destruct (buf_lib_prog !! s) eqn:Heq2; try done.
      eapply map_disjoint_Some_l in Heq2; last done. rewrite Heq1 in Heq2. by congruence.
    - apply (wp_link_progs _ _ _ _ Hlink).
  Qed.

End Proofs.