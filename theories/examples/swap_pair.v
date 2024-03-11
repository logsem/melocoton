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
Import melocoton.c_lang.notation melocoton.c_lang.proofmode.

Context `{SI:indexT}.
Context `{!ffiG Σ}.


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
Definition swap_pair_prog : lang_prog C_lang := {[ "swap_pair" := swap_pair_func ]}.

Definition swap_pair_ml_spec : protocol ML_lang.val Σ :=
  !! v1 v2 {{ True }} "swap_pair" with [ (v1, v2)%MLV ] {{ RET (v2, v1)%MLV; True }}.

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

  wp_pures.
  wp_alloc rr as "H"; first done.
  change (Z.to_nat 2) with 2. cbn. iDestruct "H" as "(H1&H2&_)". destruct rr as [rr].
  wp_pures.

  (* readfield 1 *)
  iDestruct "Hsim" as (γ lv1 lv2 ->) "(#Hptpair & #Hlv1 & #Hlv2)".
  wp_apply (wp_readfield with "[$HGC $Hptpair]"); [done..|].
  iIntros (v wlv1) "(HGC & _ & %Heq & %Hrepr1)".
  change (Z.to_nat 0) with 0 in Heq. cbn in *. symmetry in Heq. simplify_eq.
  wp_apply (wp_store with "H1"). iIntros "H1". wp_pures.

  (* readfield 2 *)
  wp_apply (wp_readfield with "[$HGC $Hptpair]"); [done..|].
  iIntros (v wlv2) "(HGC & _ & %Heq & %Hrepr2)".
  change (Z.to_nat 1) with 1 in Heq. cbn in *. symmetry in Heq. simplify_eq.
  wp_apply (wp_store with "H2"). iIntros "H2". wp_pures.

  (* registerroot 1 *)
  wp_apply (wp_registerroot with "[$HGC $H1]"); [done..|].
  iIntros "(HGC & H1r)". wp_pures.

  (* registerroot 2 *)
  wp_apply (wp_registerroot with "[$HGC $H2]"); [done..|].
  iIntros "(HGC & H2r)". wp_pures.

  (* alloc *)
  wp_apply (wp_alloc TagDefault with "HGC"); [done..|].
  iIntros (θ' γnew wnew) "(HGC & Hnew & %Hreprnew)".
  wp_pures. change (Z.to_nat 2) with 2. cbn [repeat].

  (* load from root *)
  wp_apply (load_from_root with "[HGC H1r]"); first iFrame.
  iIntros (wlv1') "(Hr1&HGC&%Hrepr1')".

  (* modify 1 *)
  wp_apply (wp_modify with "[$HGC $Hnew]"); [done..|].
  iIntros "(HGC & Hnew)". change (Z.to_nat 1) with 1. cbn.
  wp_pures.

  (* load from root *)
  wp_bind (Load _).
  wp_apply (load_from_root with "[HGC H2r]"); first iFrame.
  iIntros (wlv2') "(Hr2&HGC&%Hrepr2')".

  (* modify 2 *)
  wp_apply (wp_modify with "[$HGC $Hnew]"); [done..|].
  iIntros "(HGC & Hnew)". change (Z.to_nat 0) with 0. cbn.
  wp_pures.

  (* unregisterroot 1 *)
  wp_apply (wp_unregisterroot with "[$HGC $Hr1]"); [done..|].
  iIntros (wlv1'') "(HGC & H1 & %Hrepr1'1)".
  repr_lval_inj. wp_pures.

  (* unregisterroot 2 *)
  wp_apply (wp_unregisterroot with "[$HGC $Hr2]"); [done..|].
  iIntros (wlv2'') "(HGC & H2 & %Hrepr2'1)".
  repr_lval_inj. wp_pures.

  (* free *)
  iAssert ((Loc rr) ↦C∗ [Some wlv1'; Some wlv2'])%I with "[H1 H2]" as "Hrr".
  1: cbn; iFrame.
  wp_apply (wp_free_array' with "Hrr"); first done. iIntros "_".
  wp_pures.

  (* Finish, convert the new points-to to an immutable pointsto *)
  iMod (freeze_to_immut γnew _ θ' with "[$]") as "(HGC&#Hnew)".

  iModIntro. iApply "HΦ". iApply ("Return" with "HGC [Cont] [] []").
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
  ⊢ WP swap_pair_client at ⟨∅, swap_pair_ml_spec⟩ {{ v, ⌜∃ x : Z, v = #x ∧ x = 1⌝}}.
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
    (λ '(e, σ), mlanguage.to_val e = Some (code_int 1)).
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
(*
Check @swap_pair_adequate.
Print Assumptions swap_pair_adequate.
*)
