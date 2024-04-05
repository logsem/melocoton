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

Section C_spec.

  Import melocoton.c_interop.notation melocoton.c_lang.proofmode.

  Context `{SI:indexT}.
  Context  {Σ : gFunctors}.
  Context `{!heapG_C Σ}.
  Context `{!invG Σ}.

  Definition new_boxedint_spec_C : protocol C_intf.val Σ:=
    !!
    {{ True }}
      "new_boxedint" with []
    {{
      (a : loc), RET(#C a);
      a ↦C ( #C 0 )
    }}.

End C_spec.

Section FFI_spec.

  Import melocoton.c_interop.notation melocoton.c_lang.proofmode.

  Context `{SI:indexT}.
  Context `{!ffiG Σ}.

  Definition caml_new_boxedint_code (t : expr) : expr :=
    let: "res" := caml_alloc_custom ( ) in
    (Custom_contents ( "res" ) := #(LitInt 0));;
    "res".

  Definition caml_new_boxedint_prog : lang_prog C_lang :=
    {[ "caml_new_boxedint" := Fun [] (caml_new_boxedint_code "t") ]}.

  Definition caml_new_boxedint_spec : protocol ML_lang.val Σ :=
    !!
      {{ True }}
        "caml_new_boxedint" with []
      {{
        RET((#ML (LitBoxedInt 0))%MLV);
        True
      }}.

  Lemma new_boxedint__correct :
    (prims_proto caml_new_boxedint_spec) ⊔ new_boxedint_spec_C
    ||- caml_new_boxedint_prog :: wrap_proto caml_new_boxedint_spec.
  Proof.
    iIntros (fn ws Φ) "H". iNamed "H". iNamedProto "Hproto".
    iSplit; first done. iIntros (Φ'') "HΦ".
    iAssert (⌜length lvs = 0⌝)%I as %Hlen.
    { by iDestruct (big_sepL2_length with "Hsim") as %?. }
    destruct lvs as [|lv []]; try by (exfalso; eauto with lia); []. clear Hlen.
    destruct ws as [|w []]; try by (exfalso; apply Forall2_length in Hrepr; eauto with lia); [].
    (* apply Forall2_cons_1 in Hrepr as [Hrepr _]. *)
    cbn.
    wp_call_direct.

    (* Allocate result variable *)
    wp_apply (wp_alloc_foreign with "[$HGC]"); try eauto.
    iIntros (θ' γ w) "(HGC&Hγ&%Hγw)". wp_pures.

    (* Populate result variable *)
    wp_apply (wp_write_foreign with "[$HGC $Hγ]"); try eauto.
    iIntros "(HGC&Hγ)". wp_pures.

    iMod (freeze_to_immut).

    iModIntro.
    iApply "HΦ".
    iApply ("Return" with "[$HGC] [Cont] []").
    - by iApply "Cont".
    - cbn. iExists γ. iSplit; try eauto.
    - eauto.
Qed.

End FFI_spec.

Section ML_spec.
  Import melocoton.ml_lang.proofmode.
  Import logrel typing fundamental.

  Context `{SI:indexT}.
  Context `{!ffiG Σ}.
  Context `{!logrelG Σ}.

  Definition program_type_ctx : program_env :=
    {[ "caml_gmtime" := FunType [ TBoxedNat ] (TProd TNat TNat) ]}.

  Lemma gmtime_well_typed Δ : ⊢ ⟦ program_type_ctx ⟧ₚ* ⟨∅, caml_gmtime_spec⟩ Δ.
  Proof.
    iIntros (s vv Φ) "!> (%ats&%rt&%Heq&Hargs&Htok&HCont)".
    wp_extern. iModIntro. unfold program_type_ctx in Heq.
    apply lookup_singleton_Some in Heq as (<-&Heq). simplify_eq.
    iPoseProof (big_sepL2_length with "Hargs") as "%Heq".
    destruct vv as [|v [|??]]; cbn in Heq; try lia.
    cbn. iDestruct "Hargs" as "((%n&->)&_)".
    iSplit; first done.
    iExists n.
    do 2 (iSplit; first done).
    iIntros "!>" (tm_sec tm_min) "_". wp_pures. iModIntro.
    iApply ("HCont" with "[-Htok] Htok").
    iExists (#ML tm_sec), (#ML tm_min).
    iSplit; first done.
    iSplit; iExists _; done.
  Qed.

End ML_spec.

Section ML_Example.

  Import melocoton.ml_lang.proofmode.

  Context `{SI:indexT}.
  Context `{!ffiG Σ}.

  Definition gmtime_client : mlanguage.expr (lang_to_mlang ML_lang) :=
    (Fst (Extern "caml_gmtime" [ (Val #(LitBoxedInt 0))%MLE ])).

  Lemma ML_prog_correct_axiomatic :
    ⊢ WP gmtime_client at ⟨∅, caml_gmtime_spec⟩ {{ v, ⌜∃x : Z, v = #x⌝}}.
  Proof.
    unfold gmtime_client. wp_pures. wp_extern.
    iModIntro. cbn. iSplit; first done. iExists _.
    do 2 (iSplitR; first done). iIntros "!>" (tm_sec tm_min) "_".
    wp_pures. iModIntro. iPureIntro. by eexists.
  Qed.

End ML_Example.

