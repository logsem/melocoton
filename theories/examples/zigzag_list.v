From transfinite.base_logic.lib Require Import na_invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.combined Require Import rules adequacy.
From melocoton.linking Require Import lang weakestpre.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import basics basics_resources.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils prims_proto.
From melocoton.language Require Import weakestpre progenv.
From melocoton.c_interface Require Import notation defs resources.
From melocoton.c_interop Require Import rules notation.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.ml_lang.logrel Require fundamental logrel typing.
From melocoton.c_lang Require Import notation proofmode derived_laws.
From iris.algebra Require Import list gmap big_op.
From transfinite.base_logic.lib Require Import na_invariants ghost_var.

Definition is_empty {A} (l:list A) : bool := if l then true else false.

Definition zigzag_nil_code : C_lang.expr :=
  let: "bk" := caml_alloc_custom ( ) in
  (Custom_contents ( "bk" ) := #LitNull) ;;
  "bk".

Definition zigzag_cons_code (lhd ltl : C_lang.expr) : C_lang.expr :=
  let: "cc" := malloc (#2) in
  ("cc" +ₗ #0) <- lhd ;;
  (call: &"registerroot" with ("cc" +ₗ #0)) ;;
  ("cc" +ₗ #1) <- ltl ;;
  (call: &"registerroot" with ("cc" +ₗ #1)) ;;
  let: "bk" := caml_alloc_custom ( ) in
  (Custom_contents ( "bk" ) := "cc") ;;
  "bk".

Definition zigzag_empty_code (lst : C_lang.expr) : C_lang.expr :=
  Val_int (Custom_contents ( lst ) = #LitNull).

Definition zigzag_head_code (lst : C_lang.expr) : C_lang.expr :=
  * (Custom_contents ( lst ) +ₗ #0).

Definition zigzag_tail_code (lst : C_lang.expr) : C_lang.expr :=
  * (Custom_contents ( lst ) +ₗ #1).

Definition zigzag_pop_code (lst : C_lang.expr) : C_lang.expr :=
  let: "cc" := Custom_contents (lst) in
  Custom_contents ( lst ) := #LitNull ;;
  (call: &"unregisterroot" with ("cc" +ₗ #0)) ;;
  (call: &"unregisterroot" with ("cc" +ₗ #1)) ;;
  let: "tl" := *("cc" +ₗ #1) in (* Feature: read the value after unregistering the root *)
  free ("cc", #2) ;;
  "tl".

Definition zigzag_prog : lang_prog C_lang :=
  {[ "zigzag_nil" := Fun [] zigzag_nil_code;
     "zigzag_cons" := Fun [BNamed "hd"; BNamed "tl"] (zigzag_cons_code "hd" "tl");
     "zigzag_empty" := Fun [BNamed "lst"] (zigzag_empty_code "lst");
     "zigzag_head" := Fun [BNamed "lst"] (zigzag_head_code "lst");
     (* "zigzag_tail" := Fun [BNamed "lst"] (zigzag_tail_code "lst");
         Since our lists are uniquely owned, getting access to the tail
         is a bit harder to specify, so we elide it here :) *)
     "zigzag_pop" := Fun [BNamed "lst"] (zigzag_pop_code "lst")
  ]}.

Section Proofs.
  Import melocoton.ml_lang.notation.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ}.
  Context `{!primitive_laws.heapG_ML Σ, !wrapperG Σ, !logrelG Σ}.

  Fixpoint is_zigzag (lst : list MLval) (v : MLval) : iProp Σ :=
    ∃ i γ w, ⌜v = #(LitForeign i)⌝ ∗ γ ~foreign~ i ∗ γ ↦foreign C_intf.LitV w
             ∗ match lst with
               | nil => ⌜w = LitNull⌝
               | (v1::vr) => ∃ (a:addr) lv1 lv2 Vlst, ⌜w = a⌝ ∗ a ↦roots lv1 ∗ lv1 ~~ v1
                               ∗ (a +ₗ 1) ↦roots lv2 ∗ lv2 ~~ Vlst ∗ is_zigzag vr Vlst end.

  Import melocoton.ml_lang.notation.

  Definition zigzag_nil_spec_ML : protocol ML_lang.val Σ := λ s vv Φ,
    ( "->" ∷ ⌜s = "zigzag_nil"⌝
    ∗ "->" ∷ ⌜vv = [ ]⌝
    ∗ "HWP" ∷ ▷ (∀ vr, is_zigzag nil vr -∗ Φ vr))%I.

  Definition zigzag_cons_spec_ML : protocol ML_lang.val Σ := λ s vv Φ,
    ( ∃ hd tl tlV,
      "->" ∷ ⌜s = "zigzag_cons"⌝
    ∗ "->" ∷ ⌜vv = [ hd; tlV ]⌝
    ∗ "Htl" ∷ is_zigzag tl tlV
    ∗ "HWP" ∷ ▷ (∀ vr, is_zigzag (hd::tl) vr -∗ Φ vr))%I.

  Definition zigzag_empty_spec_ML : protocol ML_lang.val Σ := λ s vv Φ,
    ( ∃ lst lstV,
      "->" ∷ ⌜s = "zigzag_empty"⌝
    ∗ "->" ∷ ⌜vv = [ lstV ]⌝
    ∗ "Htl" ∷ is_zigzag lst lstV
    ∗ "HWP" ∷ ▷ (is_zigzag lst lstV -∗ Φ (#(is_empty lst))))%I.

  Definition zigzag_head_spec_ML : protocol ML_lang.val Σ := λ s vv Φ,
    ( ∃ hd tl lstV,
      "->" ∷ ⌜s = "zigzag_head"⌝
    ∗ "->" ∷ ⌜vv = [ lstV ]⌝
    ∗ "Htl" ∷ is_zigzag (hd::tl) lstV
    ∗ "HWP" ∷ ▷ (is_zigzag (hd::tl) lstV -∗ Φ hd))%I.

  Definition zigzag_pop_spec_ML : protocol ML_lang.val Σ := λ s vv Φ,
    ( ∃ hd tl lstV,
      "->" ∷ ⌜s = "zigzag_pop"⌝
    ∗ "->" ∷ ⌜vv = [ lstV ]⌝
    ∗ "Htl" ∷ is_zigzag (hd::tl) lstV
    ∗ "HWP" ∷ ▷ (∀ tlV, is_zigzag tl tlV -∗ is_zigzag nil lstV -∗ Φ tlV))%I.

  Import melocoton.c_lang.primitive_laws melocoton.c_lang.proofmode.

  Section InPsi.
  Context (Ψ : protocol ML_lang.val Σ).

  Lemma zigzag_nil_correct :
    prims_proto Ψ ||- zigzag_prog :: wrap_proto zigzag_nil_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    unfold progwp, zigzag_prog.
    iSplit; first done.
    destruct lvs as [|??]; try done.
    destruct ws as [|??]; decompose_Forall.
    iIntros (Φ'') "Cont2".
    wp_pure _.
    wp_apply (wp_alloc_foreign with "HGC"); [done..|].
    iIntros (θ1 γ w) "(HGC&Hγfgn&%Hrepr)". wp_pure _.
    wp_apply (wp_write_foreign with "[$HGC $Hγfgn]"); [done..|].
    iIntros "(HGC&Hγfgn)". wp_pures.
    iModIntro. iApply "Cont2".
    iDestruct "Hγfgn" as "((Hγfgn'&_)&%i&#Hi)".
    iApply ("Cont" with "HGC [Hγfgn' HWP] []"); last done.
    { iApply "HWP". iExists _, _, _. iFrame "Hi". iSplit; first done.
      iSplit; last done. iSplitL. 1: iSplit; try done. by iExists _. }
    iExists _; by iSplit.
  Qed.

  Lemma zigzag_cons_correct :
    prims_proto Ψ ||- zigzag_prog :: wrap_proto zigzag_cons_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    unfold progwp, zigzag_prog.
    iSplit; first done.
    destruct lvs as [|lvhd [|lvtl [|??]]]; try done.
    all: cbn; iDestruct "Hsim" as "(Hsimhd&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(Hsimtl&Hsim)"; try done.
    destruct ws as [|whd [|wtl [|??]]]; decompose_Forall.
    iIntros (Φ'') "Cont2".
    wp_pure _.
    wp_apply (wp_Malloc); [done..|]. iIntros (a) "Ha".
    change (Z.to_nat 2) with 2. cbn.
    iDestruct "Ha" as "(Ha0&Ha1&_)".
    wp_pures.
    wp_apply (wp_store with "Ha0"); iIntros "Ha0". do 2 wp_pure _.
    wp_apply (wp_registerroot with "[$HGC $Ha0]"); [done..|]. iIntros "(HGC&Ha0)".
    wp_pures.
    wp_apply (wp_store with "Ha1"); iIntros "Ha1". do 2 wp_pure _.
    wp_apply (wp_registerroot with "[$HGC $Ha1]"); [done..|]. iIntros "(HGC&Ha1)".
    wp_pures.
    wp_apply (wp_alloc_foreign with "HGC"); [done..|].
    iIntros (θ1 γ w) "(HGC&Hγfgn&%Hrepr)". wp_pure _.
    wp_apply (wp_write_foreign with "[$HGC $Hγfgn]"); [done..|].
    iIntros "(HGC&Hγfgn)". wp_pures.
    iModIntro. iApply "Cont2".
    iDestruct "Hγfgn" as "((Hγfgn'&_)&%i&#Hi)".
    iApply ("Cont" with "HGC [-]"); last done.
    { iApply "HWP". iExists _, _, _. iFrame "Hi". iSplit; first done. iSplitL "Hγfgn'".
      - iSplit. 1: by iSplit. by iExists _.
      - iExists _,_,_,_. iSplit; first done. rewrite loc_add_0. iFrame. by iSplit. }
    iExists _. by iSplit.
  Qed.

  Lemma zigzag_empty_correct :
    prims_proto Ψ ||- zigzag_prog :: wrap_proto zigzag_empty_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    unfold progwp, zigzag_prog.
    iSplit; first done.
    destruct lvs as [|lvhd [|??]]; try done.
    all: cbn; iDestruct "Hsim" as "(Hsimlst&Hsim)"; try done.
    destruct ws as [|wlst [|??]]; decompose_Forall.
    iIntros (Φ'') "Cont2".
    wp_pure _. rewrite {1} /is_zigzag.
    destruct lst as [|vhd vtl];
    iDestruct "Htl" as  "(%i&%γ&%ww&->&#Hi&Hγfgn&HH)".
    - iDestruct "HH" as "->".
      iDestruct "Hsimlst" as "(%γ'&->&Hi')".
      iPoseProof (lloc_own_foreign_inj with "Hi Hi' HGC") as "(HGC&%HH)".
      destruct HH as [_ Hinj]. rewrite !Hinj; last done.
      wp_apply (wp_read_foreign with "[$HGC $Hγfgn]"); [done..|]. iIntros "(HGC&Hγfgn)".
      wp_pure _.
      wp_apply (wp_int2val with "HGC"); [done..|]. iIntros (w) "(HGC&%Hw)".
      iApply "Cont2". iApply ("Cont" with "HGC [-]"); last done.
      { iApply "HWP". iExists _, _, _. iFrame "Hγfgn Hi". by iPureIntro. }
      done.
    - iDestruct "HH" as "(%a&%lv1&%lv2&%Vlst&->&Hrest)".
      iDestruct "Hsimlst" as "(%γ'&->&Hi')".
      iPoseProof (lloc_own_foreign_inj with "Hi Hi' HGC") as "(HGC&%HH)".
      destruct HH as [_ Hinj]. rewrite !Hinj; last done.
      wp_apply (wp_read_foreign with "[$HGC $Hγfgn]"); [done..|]. iIntros "(HGC&Hγfgn)".
      wp_pure _. 1: by destruct a.
      wp_apply (wp_int2val with "HGC"); [done..|]. iIntros (w) "(HGC&%Hw)".
      iApply "Cont2". iApply ("Cont" with "HGC [-]"); last done.
      { iApply "HWP". iExists _, _, _. iFrame "Hγfgn Hi".
        iSplit; first done. iExists a,lv1,lv2,Vlst; iFrame. done. }
      done.
  Qed.

  Lemma zigzag_head_correct :
    prims_proto Ψ ||- zigzag_prog :: wrap_proto zigzag_head_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    unfold progwp, zigzag_prog.
    iSplit; first done.
    destruct lvs as [|lvhd [|??]]; try done.
    all: cbn; iDestruct "Hsim" as "(Hsimlst&Hsim)"; try done.
    destruct ws as [|wlst [|??]]; decompose_Forall.
    iDestruct "Htl" as  "(%i&%γ&%ww&->&#Hi&Hγfgn&%a&%lv1&%lv2&%Vlst&->&Ha0&#Hsim0&Ha1&#Hsim1&Hrec)".
    iDestruct "Hsimlst" as "(%γ'&->&Hi')".
    iPoseProof (lloc_own_foreign_inj with "Hi Hi' HGC") as "(HGC&%HH)".
    destruct HH as [_ Hinj]. rewrite !Hinj; last done.
    iIntros (Φ'') "Cont2".
    wp_pure _.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgn]"); [done..|]. iIntros "(HGC&Hγfgn)".
    wp_pure _.
    rewrite loc_add_0.
    wp_apply (load_from_root with "[$HGC $Ha0]").
    iIntros (whd) "(Ha0&HGC&%Hrepr)".
    iApply "Cont2".
    iApply ("Cont" with "HGC [-]"); last done.
    - iApply "HWP". iExists i, γ', _. iSplit; first done. iFrame "Hi Hγfgn".
      iExists a, lv1, lv2, Vlst. iFrame "Ha0 Ha1 Hsim0 Hsim1 Hrec". done.
    - done.
    Qed.

  Lemma zigzag_pop_correct :
    prims_proto Ψ ||- zigzag_prog :: wrap_proto zigzag_pop_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    unfold progwp, zigzag_prog.
    iSplit; first done.
    destruct lvs as [|lvhd [|??]]; try done.
    all: cbn; iDestruct "Hsim" as "(Hsimlst&Hsim)"; try done.
    destruct ws as [|wlst [|??]]; decompose_Forall.
    iDestruct "Htl" as  "(%i&%γ&%ww&->&#Hi&Hγfgn&%a&%lv1&%lv2&%Vlst&->&Ha0&#Hsim0&Ha1&#Hsim1&Hrec)".
    iDestruct "Hsimlst" as "(%γ'&->&Hi')".
    iPoseProof (lloc_own_foreign_inj with "Hi Hi' HGC") as "(HGC&%HH)".
    destruct HH as [_ Hinj]. rewrite !Hinj; last done.
    iIntros (Φ'') "Cont2".
    wp_pure _.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgn]"); [done..|]. iIntros "(HGC&Hγfgn)".
    wp_pures.
    wp_apply (wp_write_foreign with "[$HGC $Hγfgn]"); [done..|]. iIntros "(HGC&Hγfgn)". wp_pures.
    rewrite loc_add_0.
    wp_apply (wp_unregisterroot with "[$HGC $Ha0]"); [done..|]. iIntros (whd) "(HGC&Ha0&%Hrepr0)".
    do 2 wp_pure _.
    wp_apply (wp_unregisterroot with "[$HGC $Ha1]"); [done..|]. iIntros (wtl) "(HGC&Ha1&%Hrepr1)".
    wp_pures.
    wp_apply (wp_load with "Ha1"). iIntros "Ha1".
    wp_pures.
    wp_apply (wp_free_array _ _ _ [_; _] with "[Ha0 Ha1]").
    { iNext. cbn. rewrite !loc_add_0. iFrame. }
    iIntros "_". wp_pures. iModIntro.
    iApply "Cont2".
    iApply ("Cont" with "HGC (HWP Hrec [Hγfgn])"); [|done..].
    iExists _, _, _; iSplit; first done. iFrame "Hγfgn Hi". done.
  Qed.
  End InPsi.

  Definition zigzag_spec_ML : protocol ML_lang.val Σ :=
    zigzag_nil_spec_ML ⊔ zigzag_cons_spec_ML ⊔ zigzag_empty_spec_ML ⊔ zigzag_head_spec_ML ⊔ zigzag_pop_spec_ML.


  Lemma zigzag_correct Ψ :
    prims_proto Ψ ||- zigzag_prog :: wrap_proto zigzag_spec_ML.
  Proof.
    iIntros (s vv Φ) "H". iNamed "H".
    iDestruct "Hproto" as "[[[[Hproto|Hproto]|Hproto]|Hproto]|Hproto]".
    - iApply zigzag_nil_correct; repeat iExists _; iFrameNamed.
    - iApply zigzag_cons_correct; repeat iExists _; iFrameNamed.
    - iApply zigzag_empty_correct; repeat iExists _; iFrameNamed.
    - iApply zigzag_head_correct; repeat iExists _; iFrameNamed.
    - iApply zigzag_pop_correct; repeat iExists _; iFrameNamed.
  Qed.

End Proofs.


