From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop.wp_prims Require Export
  (* alloc alloc_foreign *) int2val isblock length (* modify *) readfield
  read_foreign read_tag registerroot unregisterroot val2int
  (* write_foreign *).

Section Laws.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.

Lemma base_prim_correct (p : prim) e Ψ :
  p ≠ Pcallback →
  (∀ e, p ≠ Pmain e) →
  |- wrap_prog e :: prim_proto p Ψ.
Proof using.
  intros Hncb Hnmain.
  (destruct p; try by congruence); unfold prim_proto.
  - admit; apply alloc_correct.
  - apply registerroot_correct.
  - apply unregisterroot_correct.
  - admit; apply modify_correct.
  - apply readfield_correct.
  - apply val2int_correct.
  - apply int2val_correct.
  - apply isblock_correct.
  - apply read_tag_correct.
  - apply length_correct.
  - admit; apply alloc_foreign_correct.
  - admit; apply write_foreign_correct.
  - apply read_foreign_correct.
Admitted.

End Laws.
