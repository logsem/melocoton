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

Section C_prog.
Import melocoton.c_interop.notation melocoton.c_lang.proofmode.

Context `{SI:indexT}.
Context `{!ffiG Σ}.

Definition swap_pair_code (x : expr) : expr :=
  caml_init_local( );;
  CAMLlocal: "lv" in
  CAMLlocal: "f0" in
  CAMLlocal: "f1" in
  "f0" <- Field( "x", #0 );;
  "f1" <- Field( "x", #1 );;
  "lv" <- caml_alloc (#2, #0);;
  Store_field( *"lv", #0, *"f1" );;
  Store_field( *"lv", #1, *"f0" );;
  CAMLreturn ( *"lv" ).

Definition swap_pair_func : function := Fun [BNamed "x"] (swap_pair_code "x").
Definition swap_pair_prog : lang_prog C_lang := {[ "swap_pair" := swap_pair_func ]}.

Definition swap_pair_ml_spec : protocol ML_lang.val Σ :=
  !! v1 v2 {{ True }} "swap_pair" with [ (v1, v2)%MLV ] {{ RETV (v2, v1)%MLV; True }}.

Lemma swap_pair_correct :
  prims_proto swap_pair_ml_spec ||- swap_pair_prog :: wrap_proto swap_pair_ml_spec.
Proof.
  iIntros (fn ws Φ) "H". iNamed "H". iNamedProto "Hproto".
  iSplit; first done. iIntros (Φ'') "HΦ".
  iAssert (⌜length lvs = 1⌝)%I as %Hlen.
  { by iDestruct (big_sepL2_length with "Hsim") as %?. }
  destruct lvs as [|lv []]; try by (exfalso; eauto with lia); []. clear Hlen.
  destruct ws as [|w []]; try by (exfalso; apply Forall2_length in Hrepr; eauto with lia); [].
  apply Forall2_cons_1 in Hrepr as [Hrepr _].
  cbn. iDestruct "Hsim" as "[Hsim _]".
  wp_call_direct.

  wp_apply (wp_initlocalroot with "[$HGC $Hfc]"); eauto.
  iIntros (f) "(HGC&Hfc&Hlr)". wp_pures.

  wp_apply (wp_CAMLlocal with "[$HGC $Hfc $Hlr]"); eauto.
  iIntros (ℓ_lv) "(HGC&Hlv&Hfc&Hlr)". wp_pures.

  wp_apply (wp_CAMLlocal with "[$HGC $Hfc $Hlr]"); eauto.
  iIntros (ℓ_f0) "(HGC&Hf0&Hfc&Hlr)". wp_pures.

  wp_apply (wp_CAMLlocal with "[$HGC $Hfc $Hlr]"); eauto.
  iIntros (ℓ_f1) "(HGC&Hf1&Hfc&Hlr)". wp_pures.

  iDestruct "Hsim" as (γ lv1 lv2 ->) "(#Hptpair & #Hlv1 & #Hlv2)".

  (* readfield 1 *)
  wp_apply (wp_readfield with "[$HGC $Hptpair]"); [done..|].
  iIntros (v wlv1) "(HGC & _ & %Heq & %Hrepr1)".
  change (Z.to_nat 0) with 0 in Heq. cbn in *. symmetry in Heq. simplify_eq.
  wp_apply (store_to_local_root with "[$HGC $Hf0 $Hlr]"); first eauto.
  iIntros "(HGC&Hf0&Hlr)". wp_pures.

  (* readfield 2 *)
  wp_apply (wp_readfield with "[$HGC $Hptpair]"); [done..|].
  iIntros (v wlv2) "(HGC & _ & %Heq & %Hrepr2)".
  change (Z.to_nat 1) with 1 in Heq. cbn in *. symmetry in Heq. simplify_eq.
  wp_apply (store_to_local_root with "[$HGC $Hf1 $Hlr]"); first eauto.
  iIntros "(HGC&Hf1&Hlr)". wp_pures.

  (* allocate result *)
  wp_apply (wp_alloc TagDefault with "HGC"); [done..|].
  iIntros (θ' γnew wnew) "(HGC&Hnew&%Hreprnew)".
  wp_pures. change (Z.to_nat 2) with 2. cbn [repeat].
  wp_apply (store_to_local_root with "[$HGC $Hlr $Hlv]"); eauto.
  iIntros "(HGC&Hlv&Hlr)". wp_pures.

  (* storefield 1 *)
  wp_apply (load_from_local_root with "[$HGC $Hlr $Hlv]").
  iIntros (wlv1') "(Hlv&HGC&Hlr&%Hwl0)". wp_pures.
  wp_apply (load_from_local_root with "[$HGC $Hlr $Hf1]").
  iIntros (wf1) "(Hf1&HGC&Hlr&%Hf1)". wp_pures.
  wp_apply (wp_modify with "[$HGC $Hnew]"); [done..|].
  iIntros "(HGC & Hnew)". change (Z.to_nat 0) with 0. cbn.
  wp_pures.

  (* storefield 2 *)
  wp_apply (load_from_local_root with "[$HGC $Hlr $Hlv]").
  iIntros (wlv2') "(Hlv&HGC&Hlr&%Hwl1)". wp_pures.
  wp_apply (load_from_local_root with "[$HGC $Hlr $Hf0]").
  iIntros (wf0) "(Hf0&HGC&Hlr&%Hf0)". wp_pures.
  wp_apply (wp_modify with "[$HGC $Hnew]"); [done..|].
  iIntros "(HGC & Hnew)". change (Z.to_nat 1) with 1. cbn.
  wp_pures.

  (* Finish, convert the new points-to to an immutable pointsto *)
  wp_apply (load_from_local_root with "[$HGC $Hlr $Hlv]").
  iIntros (wres) "(Hres&HGC&Hlr&%Hreprres)". wp_pures.
  wp_apply (wp_unregisterlocalroot with "[$HGC $Hfc $Hlr]"); try eauto.
  iIntros "(HGC&Hfc&Hlr)". wp_pures.
  iMod (freeze_to_immut γnew _ θ' with "[$]") as "(HGC&#Hnew)".

  iModIntro. iApply "HΦ".
  iApply ("Return" $! θ' _ (OVal (Lloc γnew)) with "HGC Hfc [Cont] [] []").
  - by iApply "Cont".
  - cbn. do 3 iExists _. iFrame "Hnew Hlv1 Hlv2". done.
  - done.
Qed.

End C_prog.

Definition swap_pair_client : mlanguage.expr (lang_to_mlang ML_lang) :=
  (Fst (Fst (Extern "swap_pair" [ ((#3, (#1, #2)))%MLE ]))).

Section JustML.
Context `{SI:indexT}.
Context `{!ffiG Σ}.
Import melocoton.ml_lang.proofmode.

  Section LogRel.
  Import logrel typing fundamental.
  Context `{!logrelG Σ}.
  Context (A B : type).

  Definition program_type_ctx : program_env :=
    {[ "swap_pair" := FunType [ TProd A B ] (TProd B A) ]}.

  Lemma swap_pair_well_typed Δ : ⊢ ⟦ program_type_ctx ⟧ₚ* ⟨∅, swap_pair_ml_spec⟩ Δ.
  Proof.
    iIntros (s vv Φ) "!> (%ats&%rt&%Heq&Hargs&Htok&HCont)".
    wp_extern. iModIntro. unfold program_type_ctx in Heq.
    apply lookup_singleton_Some in Heq as (<-&Heq). simplify_eq.
    iPoseProof (big_sepL2_length with "Hargs") as "%Heq".
    destruct vv as [|v [|??]]; cbn in Heq; try lia.
    cbn. iDestruct "Hargs" as "((%w1&%w2&->&Hw1&Hw2)&_)".
    iSplit; first done. iExists _, _. do 2 (iSplit; first done). iIntros "!> _".
    wp_pures. iModIntro. iApply ("HCont" with "[-Htok] Htok").
    iExists _, _. iSplit; first done. iFrame.
  Qed.
  End LogRel.

Lemma ML_prog_correct_axiomatic :
  ⊢ WP swap_pair_client at ⟨∅, swap_pair_ml_spec⟩ {{ v, ⌜∃ x : Z, v = OVal #x ∧ x = 1⌝}}.
Proof.
  unfold swap_pair_client. wp_pures.
  wp_extern.
  iModIntro. cbn. iSplit; first done. do 2 iExists _.
  do 2 (iSplitR; first done). iIntros "!> _".
  wp_pures. iModIntro. iPureIntro. by eexists.
Qed.

End JustML.

Local Existing Instance ordinals.ordI.

Definition fullprog : mlang_prog combined_lang :=
  combined_prog swap_pair_client swap_pair_prog.

Lemma swap_pair_adequate :
  umrel.trace (mlanguage.prim_step fullprog) (LkCall "main" [], adequacy.σ_init)
    (λ '(e, σ), mlanguage.to_outcome e = Some (OVal (code_int 1))).
Proof.
  eapply umrel_upclosed.
  { eapply combined_adequacy_trace. intros Σ Hffi. split_and!.
    3: {iIntros "_". iApply ML_prog_correct_axiomatic. }
    3: apply swap_pair_correct.
    { iIntros (? Hn ?) "(% & H)". iNamedProto "H".
      exfalso. set_solver. }
    { set_solver. } }
  { by intros [? ?] (? & ? & ->). }
Qed.
