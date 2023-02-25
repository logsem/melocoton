From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources.
From melocoton.interop Require Import lang_to_mlang lang_to_mlang_wp.
From melocoton.interop Require Import wrappersem wrapper_wp wrapper_wp_utils wrapper_wp_update_laws wrapper_wp_ext_call_laws wrapper_wp_simulation.
From melocoton.ml_toy_lang Require Import lang notation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require melocoton.proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.primitive_laws.
From melocoton.c_toy_lang Require notation melocoton.proofmode.
From melocoton.mlanguage Require weakestpre.
From melocoton.interop Require Import linking linking_wp.
Import uPred.


Section C_prog.
Import melocoton.c_toy_lang.notation melocoton.c_toy_lang.melocoton.proofmode.


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
  (free ("lv", #2)) ;;
  "np"
)%E.

Definition swap_pair_func : function := Fun [BNamed "x"] (swap_pair_code "x").

Definition swap_pair_mod : gmap string function := {[ "swap_pair" := swap_pair_func]}.

Definition swap_pair_env := (mkPeC swap_pair_mod WP_ext_call_spec).

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

  (* readfield 1 *)
  wp_extern. cbn.
  iModIntro. do 5 iRight; iLeft.
  iExists _, _, _, _, _, _, _, _. unfold named. iFrame "HGC".
  do 3 (iSplitR; first done). iSplitR.
  1: iDestruct "Hptpair" as "(HL&HR)"; iApply "HL".
  do 2 (iSplitR; first done).
  iIntros (v wlv1) "HGC #Helem1". change (Z.to_nat 0) with 0. cbn -[lstore_own_elem].
  iIntros (Heq Hrepr1); injection Heq; intros <-. clear Heq.
  wp_store.

  (* readfield 2 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. do 5 iRight; iLeft.
  iExists _, _, _, _, _, _, _, _. unfold named. iFrame "HGC".
  do 3 (iSplitR; first done). iSplitR.
  1: iDestruct "Hptpair" as "(HL&HR)"; iApply "HL".
  do 2 (iSplitR; first done).
  iIntros (v wlv2) "HGC #Helem2". change (Z.to_nat 1) with 1. cbn -[lstore_own_elem].
  iIntros (Heq Hrepr2); injection Heq; intros <-. clear Heq.
  wp_store.

  (* registerroot 1 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. do 2 iRight; iLeft.
  iExists _, _, _, _. unfold named. iFrame "HGC".
  do 2 (iSplitR; first done). iSplitL "H1"; first done.
  iSplitR; first done.
  iIntros "HGC H1r".

  (* registerroot 2 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. do 2 iRight; iLeft.
  iExists _, _, _, _. unfold named. iFrame "HGC".
  do 2 (iSplitR; first done). iSplitL "H2"; first done.
  iSplitR; first done.
  iIntros "HGC H2r".

  (* alloc *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. do 6 iRight.
  iExists _, TagDefault, _. unfold named. iFrame "HGC".
  do 3 (iSplitR; first done).
  iIntros (θ' γnew wnew) "HGC Hnew %Hreprnew".
  wp_pures. change (Z.to_nat 2) with 2. cbn.

  (* load from root *)
  wp_bind (Load _).
  wp_apply (load_from_root with "[HGC H1r]"); first iFrame.
  iIntros (wlv1') "(Hr1&HGC&%Hrepr1')".

  (* modify 1 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. do 4 iRight; iLeft.
  iExists _, _, _, _, _, _, _, _. unfold named. iFrame "HGC".
  iDestruct "Hnew" as "(Hnew1&Hnew2)". iFrame "Hnew1".
  do 6 (iSplitR; first done).
  iIntros "HGC Hnew1". change (Z.to_nat 1) with 1. cbn.

  (* load from root *)
  wp_pures. wp_bind (Load _).
  wp_apply (load_from_root with "[HGC H2r]"); first iFrame.
  iIntros (wlv2') "(Hr2&HGC&%Hrepr2')".

  (* modify 2 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. do 4 iRight; iLeft.
  iExists _, _, _, _, _, _, _, _. unfold named. iFrame "HGC Hnew1".
  do 6 (iSplitR; first done).
  iIntros "HGC Hnew1". change (Z.to_nat 0) with 0. cbn.

  (* unregisterroot 1 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. do 3 iRight; iLeft.
  iExists _, _, _. unfold named. iFrame "HGC Hr1".
  do 2 (iSplitR; first done).
  iIntros (wlv1'') "HGC Hr1 %Hrepr1'1".
  destruct (repr_lval_inj _ _ _ _ Hrepr1' Hrepr1'1). (* ugly subst*) 
  clear Hrepr1'1.

  (* unregisterroot 2 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. do 3 iRight; iLeft.
  iExists _, _, _. unfold named. iFrame "HGC Hr2".
  do 2 (iSplitR; first done).
  iIntros (wlv2'') "HGC Hr2 %Hrepr2'1".
  destruct (repr_lval_inj _ _ _ _ Hrepr2' Hrepr2'1). (* ugly subst*)
  clear Hrepr2'1.

  (* free *)
  wp_pures.
  iAssert ((Loc rr) ↦∗ [Some wlv1'; Some wlv2'])%I with "[Hr1 Hr2]" as "Hrr".
  1: cbn; iFrame.
  wp_free.

  (* Finish, convert points-to *)
  wp_pures.
  iMod (freeze_to_immut γnew _ θ' with "[$]") as "(HGC&Hnew)".

  iModIntro. iExists θ', (Lloc γnew), _.
  iFrame. do 2 (iSplitR; first done).
  cbn. iExists _, _, _. iSplitR; first done. iFrame "Hnew Hlv1 Hlv2".
Qed.

Definition swap_pair_env_lifted : weakestpre.prog_environ _ Σ := (mkPeW swap_pair_mod (λ _ _ _, ⌜False⌝)%I).

Import mlanguage.weakestpre.

Lemma swap_pair_wrapped T E v1 v2:  
    at_boundary wrap_lang
 -∗ WP (Wrap.RunFunction swap_pair_func [ (v1,v2)%V ]) @ mkPeW swap_pair_mod T; E {{ v, ⌜v = (v2,v1)%V⌝ ∗ at_boundary wrap_lang }}.
Proof.
  iIntros "H".
  iApply (run_function_correct with "[] H").
  - repeat (econstructor; first (rewrite lookup_singleton_ne; done)). econstructor.
  - done.
  - iIntros (ec). iApply swap_pair_correct.
Qed. 


Definition swap_pair_ml_spec : program_specification := (
  λ s l wp, ∃ v1 v2, ⌜s = "swap_pair"⌝ ∗ ⌜l = [ (v1,v2)%V ]⌝ ∗ wp ((v2,v1)%V)
)%I.

End C_prog.

Section ML_prog.

Import melocoton.ml_toy_lang.melocoton.proofmode.

Context `{!heapGS_C Σ, !invGS_gen hlc Σ, !heapGS_ML Σ, !wrapperGS Σ, !linkGS Σ}.

Definition swap_pair_client : mlanguage.expr (lang_to_mlang ML_lang) := 
  (Extern "swap_pair" [ ((#3, (#1, #2)))%E ]).

Definition client_env := {| penv_prog := ∅; penv_proto := swap_pair_ml_spec |} : prog_environ ML_lang Σ.
Notation client_env_lifted := (penv_to_mlang client_env).

Lemma ML_prog_correct_axiomatic E : ⊢ WP swap_pair_client @ client_env ; E {{v, ⌜v = (#1,#2,#3)⌝%V}}.
Proof.
  iStartProof. unfold swap_pair_client. wp_pures.
  wp_extern.
  iModIntro. cbn. do 2 iExists _.
  do 2 (iSplitR; first done).
  wp_pures. done.
Qed.

Lemma ML_prog_correct_lifted E : ⊢ WP swap_pair_client @ penv_to_mlang client_env ; E {{v, ⌜v = (#1,#2,#3)⌝%V}}.
Proof.
  iApply wp_lang_to_mlang. iApply ML_prog_correct_axiomatic.
Qed.

Import melocoton.mlanguage.weakestpre.

Notation combined_lang := (link_lang wrap_lang (lang_to_mlang ML_lang)).
Definition linked_env : prog_environ combined_lang Σ:= {| penv_prog := fmap inl swap_pair_mod; penv_proto := λ _ _ _, ⌜False⌝%I |}.

Lemma is_linkable_swap_pair : is_link_environ swap_pair_env_lifted client_env_lifted linked_env.
Proof.
  split; cbn.
  - rewrite dom_empty_L. set_solver.
  - rewrite fmap_empty  map_union_empty. done.
  - iIntros (fn F vs Φ E H1) "%H2". done.
  - unfold swap_pair_mod.
    iIntros (fn F vs Φ E [<- <-]%lookup_singleton_Some).
    iIntros "(%v1&%v2&_&->&HΦ)".
    unfold Wrap.apply_func. iExists _. iSplitR; first done.
    iNext. iIntros "Hbound". iApply (@wp_wand with "[Hbound]").
    1: by iApply swap_pair_wrapped.
    iIntros (v) "(->&Hbound)". iFrame.
  - done.
  - unfold swap_pair_ml_spec.
    iIntros (fname vs Φ H1 H2) "(%&%&->&->&_)". unfold swap_pair_mod in H1.
    rewrite lookup_singleton in H1. congruence.
Qed.

Notation link_in_state := (link_in_state wrap_lang (lang_to_mlang ML_lang)).

Lemma linked_prog_correct_overall E : 
    link_in_state In2
 -∗ WP LkSE (Link.Expr2 swap_pair_client) @ linked_env; E 
    {{ λ v, ⌜v = (#1,#2,#3)⌝%V ∗ link_in_state Boundary }}.
Proof.
  iIntros "H". iApply (wp_link_run2 with "H []").
  1: apply is_linkable_swap_pair.
  wp_apply wp_wand.
  1: iApply ML_prog_correct_lifted.
  iIntros (v) "->". cbn. done.
Qed.

End ML_prog.

(*
Check @linked_prog_correct_overall.
Print Assumptions linked_prog_correct_overall.
*)







