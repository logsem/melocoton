From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From melocoton.language Require Import wp_link.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources.
From melocoton.interop Require Import lang_to_mlang lang_to_mlang_wp.
From melocoton.interop Require Import linking linking_wp.
From melocoton.interop Require Import wrapper_wp wrapper_wp_utils wrapper_wp_update_laws wrapper_wp_ext_call_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.primitive_laws.
From melocoton.ml_toy_lang Require notation melocoton.proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.primitive_laws.
From melocoton.c_toy_lang Require notation melocoton.proofmode.
Import uPred.

Section C_prog.

Import melocoton.ml_toy_lang.notation melocoton.c_toy_lang.notation melocoton.c_toy_lang.melocoton.proofmode.

Context `{!heapGS_C Σ, !invGS_gen hlc Σ, !primitive_laws.heapGS_ML Σ, !wrapperGS Σ}.


Definition swap_pair_code (x : expr) : expr := (
  let: "lv" := malloc (#2) in 
  ("lv" +ₗ #0 <- (call: &"readfield" with (x, Val #0))) ;;
  ("lv" +ₗ #1 <- (call: &"readfield" with (x, Val #1))) ;;
  (call: &"registerroot" with ( Var "lv" +ₗ #0 )) ;;
  (call: &"registerroot" with ( Var "lv" +ₗ #1 )) ;;
  let: "np" := (call: &"alloc" with (Val #0, Val #2)) in
  (call: &"modify" with (Var "np", Val #1, * ("lv" +ₗ #0))) ;;
  (call: &"modify" with (Var "np", Val #0, * ("lv" +ₗ #1))) ;;
  (call: &"unregisterroot" with ( Var "lv" +ₗ #0 )) ;;
  (call: &"unregisterroot" with ( Var "lv" +ₗ #1 )) ;;
  (* (free ("lv", #2)) ;; *) (* TODO: make C proofmode work with multi-free *)
  (free ("lv" +ₗ #0, #1)) ;;
  (free ("lv" +ₗ #1, #1)) ;;
  "np"
)%E.

Definition swap_pair_func : function := Fun [BNamed "x"] (swap_pair_code "x").

Definition swap_pair_env := (mkPeC {[ "swap_pair" := swap_pair_func]} WP_ext_call_spec).

Lemma swap_pair_correct v1 v2 ec E : 
    wrap_args [(v1,v2)%V] swap_pair_func ec
 -∗ WP ec @ swap_pair_env; E {{a, wrap_return (λ v, ⌜v = (v2,v1)%V⌝) a }}.
Proof.
  iIntros "(%θ&%ll&%aa&HGC&%Happly&%Hrepr&#HsimL)".
  unfold block_sim_arr.
  iPoseProof (big_sepL2_cons_inv_l with "HsimL") as "(%l&%lr&->&Hsim&HsimL')".
  iPoseProof (big_sepL2_nil_inv_l with "HsimL'") as "->". iClear "HsimL' HsimL".
  cbn. iDestruct "Hsim" as "(%γpair&%lv1&%lv2&->&Hptpair&Hlv1&Hlv2)".
  destruct (Forall2_cons_inv_l _ _ _ _ Hrepr) as (w&aa'&Hγw&HH&->).
  pose proof (Forall2_nil_inv_l _ _ HH); subst aa'. clear HH Hrepr.
  cbn in Happly.
  injection Happly; intros <-; clear Happly.
  solve_lookup_fixed.
  wp_alloc rr as "H". 1: done.
  change (Z.to_nat 2) with 2. cbn. iDestruct "H" as "(H1&H2&_)". destruct rr as [rr].
  wp_pures.

  wp_extern. cbn.
  iModIntro. do 5 iRight; iLeft.
  iExists _, _, _, _, _, _, _, _. unfold named. iFrame "HGC".
  do 3 (iSplitR; first done). iSplitR.
  1: iDestruct "Hptpair" as "(HL&HR)"; iApply "HL".
  do 2 (iSplitR; first done).
  iIntros (v wlv1) "HGC #Helem1". change (Z.to_nat 0) with 0. cbn -[lstore_own_elem].
  iIntros (Heq Hrepr1); injection Heq; intros <-. clear Heq.

  wp_store. wp_pures.
  wp_extern. cbn.
  iModIntro. do 5 iRight; iLeft.
  iExists _, _, _, _, _, _, _, _. unfold named. iFrame "HGC".
  do 3 (iSplitR; first done). iSplitR.
  1: iDestruct "Hptpair" as "(HL&HR)"; iApply "HL".
  do 2 (iSplitR; first done).
  iIntros (v wlv2) "HGC #Helem2". change (Z.to_nat 1) with 1. cbn -[lstore_own_elem].
  iIntros (Heq Hrepr2); injection Heq; intros <-. clear Heq.
  
  wp_store. wp_pures.
  wp_extern. cbn.
  iModIntro. do 2 iRight; iLeft.
  iExists _, _, _, _. unfold named. iFrame "HGC".
  do 2 (iSplitR; first done). iSplitL "H1"; first done.
  iSplitR; first done.
  iIntros "HGC H1r".

  wp_pures.
  wp_extern. cbn.
  iModIntro. do 2 iRight; iLeft.
  iExists _, _, _, _. unfold named. iFrame "HGC".
  do 2 (iSplitR; first done). iSplitL "H2"; first done.
  iSplitR; first done.
  iIntros "HGC H2r".

  wp_pures.
  wp_extern. cbn.
  iModIntro. do 6 iRight.
  iExists _, TagDefault, _. unfold named. iFrame "HGC".
  do 3 (iSplitR; first done).
  iIntros (θ' γnew wnew) "HGC Hnew %Hreprnew".
  wp_pures. change (Z.to_nat 2) with 2. cbn.

  wp_bind (Load _).
  wp_apply (load_from_root with "[HGC H1r]"); first iFrame.
  iIntros (wlv1') "(Hr1&HGC&%Hrepr1')".

  wp_pures.
  wp_extern. cbn.
  iModIntro. do 4 iRight; iLeft.
  iExists _, _, _, _, _, _, _, _. unfold named. iFrame "HGC".
  iDestruct "Hnew" as "(Hnew1&Hnew2)". iFrame "Hnew1".
  do 6 (iSplitR; first done).
  iIntros "HGC Hnew1". change (Z.to_nat 1) with 1. cbn.

  wp_pures. wp_bind (Load _).
  wp_apply (load_from_root with "[HGC H2r]"); first iFrame.
  iIntros (wlv2') "(Hr2&HGC&%Hrepr2')".

  wp_pures.
  wp_extern. cbn.
  iModIntro. do 4 iRight; iLeft.
  iExists _, _, _, _, _, _, _, _. unfold named. iFrame "HGC Hnew1".
  do 6 (iSplitR; first done).
  iIntros "HGC Hnew1". change (Z.to_nat 0) with 0. cbn.

  wp_pures.
  wp_extern. cbn.
  iModIntro. do 3 iRight; iLeft.
  iExists _, _, _. unfold named. iFrame "HGC Hr1".
  do 2 (iSplitR; first done).
  iIntros (wlv1'') "HGC Hr1 %Hrepr1'1".
  destruct (repr_lval_inj _ _ _ _ Hrepr1' Hrepr1'1). (* ugly subst*) 
  clear Hrepr1'1.

  wp_pures.
  wp_extern. cbn.
  iModIntro. do 3 iRight; iLeft.
  iExists _, _, _. unfold named. iFrame "HGC Hr2".
  do 2 (iSplitR; first done).
  iIntros (wlv2'') "HGC Hr2 %Hrepr2'1".
  destruct (repr_lval_inj _ _ _ _ Hrepr2' Hrepr2'1). (* ugly subst*)
  clear Hrepr2'1.

  wp_pures. wp_free.
  wp_pures. wp_free.
  wp_pures.

  iMod (freeze_to_immut γnew _ θ' with "[$]") as "(HGC&Hnew)".

  iModIntro. iExists θ', (Lloc γnew), _.
  iFrame. do 2 (iSplitR; first done).
  cbn. iExists _, _, _. iSplitR; first done. iFrame "Hnew Hlv1 Hlv2".
Qed.

End C_prog.

Section ML_prog.

Import melocoton.ml_toy_lang.lang melocoton.ml_toy_lang.notation melocoton.ml_toy_lang.melocoton.proofmode.

Context `{!heapGS_ML Σ, !invGS_gen hlc Σ}.

Definition swap_pair_client : expr := 
  (Extern "swap_pair" [ (((#2, #3), #1))%E ]).

Definition swap_pair_ml_spec : program_specification := (
  λ s l wp, ∃ v1 v2, ⌜s = "swap_pair"⌝ ∗ ⌜l = [ (v1,v2)%V ]⌝ ∗ wp ((v2,v2)%V)
)%I.

(* TODO: instantiate linking *)

End ML_prog.







