From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.ml_lang.logrel Require logrel typing fundamental.
From melocoton.interop Require Import basics basics_resources.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils wp_ext_call_laws wp_simulation.
From melocoton.c_interop Require Import rules.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.ml_lang Require proofmode.
From melocoton.c_lang Require notation proofmode.
From melocoton.mlanguage Require Import progenv.
From melocoton.mlanguage Require weakestpre.
From melocoton.linking Require Import lang weakestpre.
From melocoton.combined Require Import adequacy rules.

Section FFI_spec.

  Import melocoton.c_interop.notation melocoton.c_lang.proofmode.

  Context `{SI:indexT}.
  Context `{!ffiG Σ}.

  Definition caml_unit_code : expr :=
    caml_init_local( );;
    CAMLlocal: "res" in
    "res" <- Val_int(#C 0);;
    *"res".

  Definition caml_unit_prog : lang_prog C_lang :=
    {[ "caml_unit" := Fun [] caml_unit_code ]}.

  Definition caml_unit_spec : protocol ML_lang.val Σ :=
    !! {{ True }} "caml_unit" with ([]) {{ RETV #ML 0; True }}.

  Lemma caml_unit_correct :
    prims_proto caml_unit_spec ||- caml_unit_prog :: wrap_proto caml_unit_spec.
  Proof.
    iIntros (fn ws Φ) "H". iNamed "H". iNamedProto "Hproto".
    iSplit; first done. iIntros (Φ'') "HΦ".
    iAssert (⌜length lvs = 0⌝)%I as %Hlen.
    { by iDestruct (big_sepL2_length with "Hsim") as %?. }
    destruct lvs as [|lv []]; try by (exfalso; eauto with lia); []. clear Hlen.
    destruct ws as [|w []]; try by (exfalso; apply Forall2_length in Hrepr; eauto with lia); [].
    cbn.
    wp_call_direct.

    (* Declare result variable *)
    wp_apply (wp_initlocalroot with "[$HGC $Hfc]"); eauto.
    iIntros (f) "(HGC&Hfc&Hlr)". wp_pures.

    wp_apply (wp_CAMLlocal with "[$HGC $Hfc $Hlr]"); eauto.
    iIntros (ℓ) "(HGC&Hℓ&Hfc&Hlr)". wp_pures.
    wp_apply (wp_int2val with "HGC"); [done..|]. iIntros (w) "(HGC&%Hw)".
Abort.

End FFI_spec.
