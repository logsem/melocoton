From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop.wp_prims Require Export
  alloc alloc_foreign int2val modify readfield read_foreign
  registerroot unregisterroot val2int write_foreign.

Section Laws.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.

Lemma base_prim_correct (p : prim) E e Ψ :
  p ≠ Pcallback →
  (∀ e, p ≠ Pmain e) →
  |- prims_prog e @ E :: prim_proto p E Ψ.
Proof using.
  intros Hncb Hnmain.
  (destruct p; try by congruence); unfold prim_proto.
  - apply alloc_correct.
  - apply registerroot_correct.
  - apply unregisterroot_correct.
  - apply modify_correct.
  - apply readfield_correct.
  - apply val2int_correct.
  - apply int2val_correct.
  - apply alloc_foreign_correct.
  - apply write_foreign_correct.
  - apply read_foreign_correct.
Qed.

End Laws.
