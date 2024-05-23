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

  Definition gmtime_spec_C : protocol C_intf.val Σ:=
    !! (w : Z)
    {{ True }}
      "gmtime" with ([ #C w ])
    {{
      (a : loc) (tm_sec : Z) (tm_min : Z), RET(#C a);
      a ↦C∗ [ #C tm_sec; #C tm_min ]
    }}.

End C_spec.

Section FFI_spec.

  Import melocoton.c_interop.notation melocoton.c_lang.proofmode.

  Context `{SI:indexT}.
  Context `{!ffiG Σ}.

  Definition caml_gmtime_code (t : expr) : expr :=
    CAMLlocal: "res" in
    let: "timer" := BoxedInt_val (t) in
    let: "tm"    := (call: &"gmtime" with ("timer")) in
    "res" <- caml_alloc (#2, #0);;

    let: "tm_sec" := Val_int ( *( "tm" +ₗ #0 ) )  in
    let: "tm_min" := Val_int ( *( "tm" +ₗ #1 ) )  in

    Store_field( *"res", #0, "tm_sec" );;
    Store_field( *"res", #1, "tm_min" );;

    CAMLreturn: *"res" unregistering [ "res" ].

  Definition caml_gmtime_prog : lang_prog C_lang :=
    {[ "caml_gmtime" := Fun [BNamed "t"] (caml_gmtime_code "t") ]}.

  Definition caml_gmtime_spec : protocol ML_lang.val Σ :=
    !! (t : Z)
      {{ True }}
        "caml_gmtime" with [(#ML (ML_lang.LitBoxedInt t))]
      {{
        (tm_sec : Z) (tm_min : Z), RET((#ML tm_sec, #ML tm_min)%MLV);
        True
      }}.

  Lemma gmtime_correct :
    (prims_proto caml_gmtime_spec) ⊔ gmtime_spec_C
    ||- caml_gmtime_prog :: wrap_proto caml_gmtime_spec.
  Proof.
    iIntros (fn ws Φ) "H". iNamed "H". iNamedProto "Hproto".
    iSplit; first done. iIntros (Φ'') "HΦ".
    iAssert (⌜length lvs = 1⌝)%I as %Hlen.
    { by iDestruct (big_sepL2_length with "Hsim") as %?. }
    destruct lvs as [|lv []]; try by (exfalso; eauto with lia); []. clear Hlen.
    destruct ws as [|w []]; try by (exfalso; apply Forall2_length in Hrepr; eauto with lia); [].
    apply Forall2_cons_1 in Hrepr as [Hrepr _].
    cbn.
    iDestruct "Hsim" as "[Hγ _]".
    iDestruct "Hγ" as (γ) "[-> Hγ]".
    wp_call_direct.
    wp_apply wp_allocframe. iIntros (l) "Hl".
    unfold allocate_frame. cbn. wp_pures.

    (* Declare result variable *)
    wp_apply (wp_int2val with "[$]"); try done.
    wp_apply (wp_CAMLlocal with "HGC"); eauto. iIntros (ℓ) "(HGC&Hℓ)". wp_pures.

    (* Call stdlib gmtime *)
    wp_apply (wp_read_foreign with "[$HGC $Hγ]"); try eauto.
    iIntros "(HGC&_)".
    wp_pures.
    wp_extern. iModIntro. iRight.
    iSplit; first done.
    iExists t; do 2 (iSplit; first done).
    iIntros (a tm_sec tm_min). iNext.
    cbn.
    iIntros "(Ha0&Ha1&_)". wp_pures.

    (* Allocate result variable *)
    wp_apply (wp_alloc (TagDefault) with "HGC"); try done; auto.
    iIntros (θ' γ' w0') "(HGC&Hγ'&%H2)".
    wp_apply (store_to_root with "[$HGC $Hℓ]"); try done.
    iIntros "(HGC&Hℓ)". wp_pures.

    (* Convert tm_sec to ml int *)
    wp_apply (wp_load with "[Ha0]"); try auto.
    iIntros "Ha0".
    wp_apply (wp_int2val with "HGC"); try auto.
    iIntros (w0) "(HGC&%Htms)". wp_pures.

    (* Convert tm_min to ml int *)
    wp_apply (wp_load with "[Ha1]"); try auto.
    iIntros "Ha1".
    wp_apply (wp_int2val with "HGC"); try auto.
    iIntros (w1) "(HGC&%Htmm)". wp_pures.

    (* Load tm_sec *)
    wp_apply (load_from_root with "[$HGC $Hℓ]").
    iIntros (w2) "(Hℓ&HGC&%Hγ2)".
    wp_apply (wp_modify with "[$HGC $Hγ']"); try eauto.
    1: simpl; done.
    iIntros "(HGC&Hγ')". wp_pures.

    (* Load tm_min *)
    wp_apply (load_from_root with "[$HGC $Hℓ]").
    iIntros (w3) "(Hℓ&HGC&%Hγ3)".
    wp_apply (wp_modify with "[$HGC $Hγ']"); try eauto.
    1: simpl; done.
    iIntros "(HGC&Hγ')". wp_pures.

    (* Return *)
    wp_apply (load_from_root with "[$HGC $Hℓ]").
    iIntros (w4) "(Hℓ&HGC&Hγ4)". wp_pures.

    wp_apply (wp_unregisterroot with "[$HGC $Hℓ]"); try eauto.
    iIntros (w5) "(HGC&hℓ&%Hγ5)". wp_pures.
    wp_free. wp_pures.

    iMod (freeze_to_immut γ' _ θ' with "[$]") as "(HGC&#Hγ')".

    wp_free.

    iModIntro.
    iApply "HΦ".
    iApply ("Return" with "[$HGC] [Cont] []").
    - by iApply "Cont".
    - cbn. iExists γ'. iExists _, _. iSplit; try eauto.
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
    ⊢ WP gmtime_client at ⟨∅, caml_gmtime_spec⟩ {{ v, ⌜∃x : Z, v = OVal #x⌝}}.
  Proof.
    unfold gmtime_client. wp_pures. wp_extern.
    iModIntro. cbn. iSplit; first done. iExists _.
    do 2 (iSplitR; first done). iIntros "!>" (tm_sec tm_min) "_".
    wp_pures. iModIntro. iPureIntro. by eexists.
  Qed.

End ML_Example.

