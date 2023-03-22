From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils wp_ext_call_laws wp_simulation.
From melocoton.c_interop Require Import rules.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import lang_instantiation.
From melocoton.ml_lang Require proofmode.
From melocoton.c_lang Require notation proofmode.
From melocoton.mlanguage Require weakestpre.
From melocoton.linking Require Import lang weakestpre.


Section C_prog.
Import melocoton.c_lang.notation melocoton.c_lang.proofmode.


Context `{!heapGS_C Σ, !heapGS_ML Σ, !invGS_gen hlc Σ, !primitive_laws.heapGS_ML Σ, !wrapperGS Σ}.


Definition swap_pair_code (x : expr) : expr :=
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
  "np".

Definition swap_pair_func : function := Fun [BNamed "x"] (swap_pair_code "x").

Definition swap_pair_mod : gmap string function := {[ "swap_pair" := swap_pair_func ]}.

Definition swap_pair_ml_spec : @program_specification _ ML_lang _ _ _ _ := (
  λ s l wp, ∃ v1 v2, ⌜s = "swap_pair"⌝ ∗ ⌜l = [ (v1,v2)%MLV ]⌝ ∗ wp ((v2,v1)%MLV)
)%I.

Definition swap_pair_env : language.weakestpre.prog_environ C_lang Σ :=
  ⟨ swap_pair_mod, (proto_prims_in_C ∅ swap_pair_ml_spec) ⟩.

Lemma swap_pair_correct E f vs Φ :
    wrap_proto swap_pair_ml_spec f vs Φ
 -∗ ∃ x, ⌜vs = [x]⌝ ∗ WP swap_pair_code (Val x) @ swap_pair_env; E {{a, Φ a }}.
Proof.
  iIntros "H". iNamed "H".
  iDestruct "Hproto" as (v1 v2) "(->&->&Hψ)".
  rewrite /of_call /of_class /=.
  unfold block_sim_arr.
  iPoseProof (big_sepL2_cons_inv_l with "Hsim") as "(%l&%lr&->&Hsim&HsimL')".
  iPoseProof (big_sepL2_nil_inv_l with "HsimL'") as "->".
  cbn. iDestruct "Hsim" as "(%γpair&%lv1&%lv2&->&#Hptpair&#Hlv1&#Hlv2)".
  destruct (Forall2_cons_inv_l _ _ _ _ Hrepr) as (w&aa'&Hγw&HH&Hx).
  pose proof (Forall2_nil_inv_l _ _ HH); subst aa'. simplify_eq. clear HH Hrepr.
  unfold swap_pair_code.
  iExists _; iSplit; first done.
  wp_alloc rr as "H". 1: done.
  change (Z.to_nat 2) with 2. cbn. iDestruct "H" as "(H1&H2&_)". destruct rr as [rr].
  wp_pures.


  (* readfield 1 *)
  wp_extern. cbn.
  iModIntro. (iExists _; iSplit; first (iPureIntro; econstructor)).
  iExists _, _, _, _, _, _, _, _. unfold named. iFrame "HGC".
  do 2 (iSplitR; first done). iFrame "Hptpair".
  do 2 (iSplitR; first done).
  iIntros "!>" (v wlv1) "HGC #Helem1". change (Z.to_nat 0) with 0. cbn -[lstore_own_elem].
  iIntros (Heq Hrepr1); injection Heq; intros <-. clear Heq.
  wp_store.

  (* readfield 2 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. (iExists _; iSplit; first (iPureIntro; econstructor)).
  iExists _, _, _, _, _, _, _, _. unfold named. iFrame "HGC".
  do 2 (iSplitR; first done). iFrame "Hptpair".
  do 2 (iSplitR; first done).
  iIntros "!>" (v wlv2) "HGC #Helem2". change (Z.to_nat 1) with 1. cbn -[lstore_own_elem].
  iIntros (Heq Hrepr2); injection Heq; intros <-. clear Heq.
  wp_store.

  (* registerroot 1 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. (iExists _; iSplit; first (iPureIntro; econstructor)).
  iExists _, _, _, _. unfold named. iFrame "HGC".
  iSplitR; first done. iSplitL "H1"; first done.
  iSplitR; first done.
  iIntros "!> HGC H1r".

  (* registerroot 2 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. (iExists _; iSplit; first (iPureIntro; econstructor)).
  iExists _, _, _, _. unfold named. iFrame "HGC".
  iSplitR; first done. iSplitL "H2"; first done.
  iSplitR; first done.
  iIntros "!> HGC H2r".

  (* alloc *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. (iExists _; iSplit; first (iPureIntro; econstructor)).
  iExists _, TagDefault, _. unfold named. iFrame "HGC".
  do 2 (iSplitR; first done).
  iIntros "!>" (θ' γnew wnew) "HGC Hnew %Hreprnew".
  wp_pures. change (Z.to_nat 2) with 2. cbn.

  (* load from root *)
  wp_bind (Load _).
  wp_apply (load_from_root with "[HGC H1r]"); first iFrame.
  iIntros (wlv1') "(Hr1&HGC&%Hrepr1')".

  (* modify 1 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. (iExists _; iSplit; first (iPureIntro; econstructor)).
  do 9 iExists _. unfold named. iFrame "HGC Hnew".
  do 6 (iSplitR; first done).
  iIntros "!> HGC Hnew1". change (Z.to_nat 1) with 1. cbn.

  (* load from root *)
  wp_pures. wp_bind (Load _).
  wp_apply (load_from_root with "[HGC H2r]"); first iFrame.
  iIntros (wlv2') "(Hr2&HGC&%Hrepr2')".

  (* modify 2 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. (iExists _; iSplit; first (iPureIntro; econstructor)).
  do 9 iExists _. unfold named. iFrame "HGC Hnew1".
  do 6 (iSplitR; first done).
  iIntros "!> HGC Hnew1". change (Z.to_nat 0) with 0. cbn.

  (* unregisterroot 1 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. (iExists _; iSplit; first (iPureIntro; econstructor)).
  iExists _, _, _. unfold named. iFrame "HGC Hr1".
  iSplitR; first done.
  iIntros "!>" (wlv1'') "HGC Hr1 %Hrepr1'1".
  destruct (repr_lval_inj _ _ _ _ Hrepr1' Hrepr1'1). (* ugly subst*) 
  clear Hrepr1'1.

  (* unregisterroot 2 *)
  wp_pures.
  wp_extern. cbn.
  iModIntro. (iExists _; iSplit; first (iPureIntro; econstructor)).
  iExists _, _, _. unfold named. iFrame "HGC Hr2".
  iSplitR; first done.
  iIntros "!>" (wlv2'') "HGC Hr2 %Hrepr2'1".
  destruct (repr_lval_inj _ _ _ _ Hrepr2' Hrepr2'1). (* ugly subst*)
  clear Hrepr2'1.

  (* free *)
  wp_pures.
  iAssert ((Loc rr) ↦C∗ [Some wlv1'; Some wlv2'])%I with "[Hr1 Hr2]" as "Hrr".
  1: cbn; iFrame.
  wp_free.

  (* Finish, convert points-to *)
  wp_pures.
  iMod (freeze_to_immut γnew _ θ' with "[$]") as "(HGC&#Hnew)".

  iModIntro. iApply ("Cont" with "HGC Hψ [] []").
  - cbn. do 3 iExists _. iFrame "Hnew Hlv1 Hlv2". done.
  - done.
Qed.

End C_prog.

Section ML_prog.

Import melocoton.c_lang.primitive_laws.
Import melocoton.ml_lang.proofmode.

Context `{!heapGS_C Σ, !invGS_gen hlc Σ, !heapGS_ML Σ, !wrapperGS Σ, !linkGS Σ}.

Definition swap_pair_client : mlanguage.expr (lang_to_mlang ML_lang) := 
  (Extern "swap_pair" [ ((#3, (#1, #2)))%MLE ]).

Definition client_env : prog_environ ML_lang Σ := ⟨ ∅, swap_pair_ml_spec ⟩.
Definition client_env_wrapped := (wrap_penv client_env).

Lemma ML_prog_correct_axiomatic E : ⊢ WP swap_pair_client @ client_env ; E {{v, ⌜v = (#1,#2,#3)⌝%MLV}}.
Proof.
  iStartProof. unfold swap_pair_client. wp_pures.
  wp_extern.
  iModIntro. cbn. do 2 iExists _.
  do 2 (iSplitR; first done).
  wp_pures. done.
Qed.

Import melocoton.mlanguage.weakestpre.

Notation combined_lang := (link_lang wrap_lang (lang_to_mlang C_lang)).
Definition swap_pair_env_lifted := penv_to_mlang swap_pair_env.

Lemma swap_pair_correct_lifted E f vs Φ :
    wrap_proto swap_pair_ml_spec f vs Φ
 -∗ ∃ x, ⌜vs = [x]⌝ ∗ WP (swap_pair_code (C_lang.Val x) : expr (lang_to_mlang (C_lang))) @ swap_pair_env_lifted ; E {{a, Φ a }}.
Proof.
  iIntros "H".
  iPoseProof (swap_pair_correct with "H") as (x ->) "HWP".
  iExists _; iSplit; first done.
  by iApply wp_lang_to_mlang.
Qed.

Definition linked_env : prog_environ combined_lang Σ :=
  ⟪ fmap inl prims.prims_prog ∪ fmap inr swap_pair_mod,
    λ _ _ _, ⌜False⌝%I ⟫.

Lemma is_linkable_swap_pair : is_link_environ client_env_wrapped swap_pair_env_lifted linked_env.
Proof.
  split.
  - rewrite !dom_insert_L !dom_empty_L. set_solver.
  - done.
  - cbn. unfold swap_pair_mod.
    iIntros (fn F vs Φ E [<- <-]%lookup_singleton_Some) "HH".
    iPoseProof (swap_pair_correct_lifted with "HH") as (w ->) "HWP".
    rewrite /C_lang.apply_function /swap_pair_func.
    cbn -[C_lang.subst_all].
    iExists _; iSplit; first done.
    iNext. iIntros "Hbound". iApply (wp_wand with "[HWP]").
    { solve_lookup_fixed; iApply "HWP". }
    iIntros (v) "H". iFrame.
  - iIntros (fname func vs Φ E Hfunc) "Hproto".
    iExists _; iSplit; first done.
    iApply bi.later_intro.
    iIntros "Hb". iApply (@wp_wand with "[Hb Hproto]");
    first iApply (wp_base_primitives with "[] [Hproto]").
    + done.
    + iIntros (fn_name vs' Φ' Hprims) "HH".
      cbn. iDestruct "HH" as "(%&%&->&_)". inversion Hprims. inversion H. 
    + cbn. iDestruct "Hproto" as "(%pr&%HH1&HH2)".
      apply prims.lookup_prims_prog_Some in Hfunc.
      pose proof (prims.is_prim_inj _ _ _ HH1 Hfunc) as ->.
      iApply proto_prim_mask_mono; last done.
      apply namespaces.coPset_empty_subseteq.
    + done.
    + iIntros (v) "(Hb&Hv)". iFrame.
  - iIntros (fn vs Φ HH1 HH2) "H". iNamed "H".
    iDestruct "Hproto" as (v1 v2 -> ->) "H".
    rewrite lookup_insert in HH2; done.
  - iIntros (fn vs Φ HH1 HH2) "H".
    rewrite /=. iDestruct "H" as (prim HH%prims.lookup_prims_prog_Some) "H".
    rewrite HH in HH1. done.
Qed.

Notation link_in_state := (link_in_state wrap_lang (lang_to_mlang C_lang)).
(*
Lemma linked_prog_correct_overall E : 
    link_in_state In1
 -∗ WP LkSE (Link.Expr1 swap_pair_client) @ linked_env; E 
    {{ λ v, ⌜v = (#1,#2,#3)⌝%V ∗ link_in_state Boundary }}.
Proof.
  iIntros "H". iApply (wp_link_run2 with "H []").
  1: apply is_linkable_swap_pair.
  wp_apply wp_wand.
  1: iApply ML_prog_correct_lifted.
  iIntros (v) "->". cbn. done.
Qed.
*)
End ML_prog.

(*
Check @linked_prog_correct_overall.
Print Assumptions linked_prog_correct_overall.
*)
