From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils wp_ext_call_laws wp_simulation.
From melocoton.c_interop Require Import rules.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.c_lang Require Import notation proofmode.
From melocoton.mlanguage Require Import progenv.
From melocoton.mlanguage Require weakestpre.
From melocoton.linking Require Import lang weakestpre.
From melocoton.combined Require Import adequacy rules.
From stdpp Require Import fin_maps.

Context `{SI:indexT}.
Context `{!ffiG Σ}.

Definition caml_id : expr :=
  let: "e2" := &: "e" in
  "e".

Definition caml_id_prog : lang_prog C_lang :=
  {[ "caml_id" := Fun [BNamed "e"] caml_id ]}.

Definition caml_id_spec : protocol ML_lang.val Σ :=
  !! e {{ True }} "caml_id" with [e] {{ RET(e); True }}.

Lemma caml_id_correct:
  prims_proto caml_id_spec ||- caml_id_prog :: wrap_proto caml_id_spec.
Proof.
  iIntros (fn ws Φ) "H". iNamed "H". iNamedProto "Hproto".
  iSplit; first done. iIntros (Φ'') "HΦ".
  iAssert (⌜length lvs = 1⌝)%I as %Hlen.
  { by iDestruct (big_sepL2_length with "Hsim") as %?. }
  destruct lvs as [|lv []]; try by (exfalso; eauto with lia); []. clear Hlen.
  destruct ws as [|w []]; try by (exfalso; apply Forall2_length in Hrepr; eauto with lia); [].
  apply Forall2_cons_1 in Hrepr as [Hrepr _].
  cbn.
  iDestruct "Hsim" as "[He _ ]".
  wp_call_direct.
  wp_apply (wp_allocframe); try eauto.

  (* Allocate result variable *)
  wp_apply (wp_alloc_foreign with "[$HGC]"); try eauto.
  iIntros (θ' γ w) "(HGC&Hγ&%Hγw)". wp_pures.

  (* Populate result variable *)
  wp_apply (wp_write_foreign with "[$HGC $Hγ]"); try eauto.
  iIntros "(HGC&Hγ)". wp_pures.

  iMod (freeze_foreign_to_immut γ θ' _ with "[$]") as "(HGC&#Hγ)".

  iModIntro.
  iApply "HΦ".
  iApply ("Return" with "[$HGC] [Cont] []").
  - by iApply "Cont".
  - cbn. iExists γ. iSplit; try eauto.
  - eauto.
Qed.

