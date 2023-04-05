From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
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
From melocoton.interop Require Import adequacy.


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

Definition swap_pair_ml_spec : protocol ML_lang.val Σ := (
  λ s l wp, ∃ v1 v2, ⌜s = "swap_pair"⌝ ∗ ⌜l = [ (v1,v2)%MLV ]⌝ ∗ wp ((v2,v1)%MLV)
)%I.

Lemma swap_pair_correct E :
  prims_proto E swap_pair_ml_spec ||- swap_pair_prog @ E :: wrap_proto swap_pair_ml_spec.
Proof.
  iIntros (fn ws Φ) "H". iNamed "H".
  iDestruct "Hproto" as (v1 v2) "(->&->&Hψ)".
  rewrite /progwp lookup_insert.
  iAssert (⌜length lvs = 1⌝)%I as %Hlen.
  { by iDestruct (big_sepL2_length with "Hsim") as %?. }
  destruct lvs as [|lv []]; try by (exfalso; eauto with lia); []. clear Hlen.
  destruct ws as [|w []]; try by (exfalso; apply Forall2_length in Hrepr; eauto with lia); [].
  apply Forall2_cons_1 in Hrepr as [Hrepr _].
  do 2 (iExists _; iSplit; first done). iNext. cbn.
  iDestruct "Hsim" as "[Hsim _]".

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

  iModIntro. iApply ("Cont" with "HGC Hψ [] []").
  - cbn. do 3 iExists _. iFrame "Hnew Hlv1 Hlv2". done.
  - done.
Qed.

End C_prog.

Definition swap_pair_client : mlanguage.expr (lang_to_mlang ML_lang) :=
  (Fst (Fst (Extern "swap_pair" [ ((#3, (#1, #2)))%MLE ]))).

Section JustML.
Context `{SI:indexT}.
Context `{!ffiG Σ}.

(* Import melocoton.c_lang.primitive_laws. *)
Import melocoton.ml_lang.proofmode.

Lemma ML_prog_correct_axiomatic E :
  {{{ True }}} swap_pair_client @ ⟨∅, swap_pair_ml_spec⟩ ; E {{{ x, RET (#x); ⌜x = 1%Z⌝}}}.
Proof.
  unfold swap_pair_client. iIntros (? _) "HΦ". wp_pures.
  wp_extern.
  iModIntro. cbn. do 2 iExists _.
  do 2 (iSplitR; first done).
  wp_pures. iModIntro. by iApply "HΦ".
Qed.

End JustML.

Section FullProg.
Import melocoton.mlanguage.weakestpre.
Context `{SI:indexT}.
Context `{!ffiG Σ}.

Definition fullprog : mlang_prog (link_lang wrap_lang C_mlang) :=
  link_prog wrap_lang C_mlang (wrap_prog swap_pair_client) swap_pair_prog.

Lemma fullprog_correct :
  ⊥ |- fullprog :: main_proto (λ ret, ret = 1).
Proof.
  eapply prog_triple_mono_r; swap 1 2.
  { eapply link_close_correct.
    { rewrite dom_prims_prog. set_solver. }
    3: { apply wrap_correct.
         2: { iIntros (? _) "HΦ". by iApply ML_prog_correct_axiomatic. }
         { iIntros (? Hn ?) "(% & H)". iDestruct "H" as (? ? ->) "H".
           exfalso. set_solver. } }
    3: { apply lang_to_mlang_correct, swap_pair_correct. }
    1: done.
    apply proto_refines_join_l. }
  { rewrite -proto_refines_join_l -proto_refines_join_r //. }
Qed.
End FullProg.

Section Adequacy.
  Existing Instance ordinals.ordI.

  Lemma swap_pair_adequate :
    umrel.trace (mlanguage.prim_step fullprog) (LkCall "main" [], adequacy.σ_init)
      (λ '(e, σ), mlanguage.to_val e = Some (code_int 1)).
  Proof.
    eapply umrel_upclosed.
    1: eapply (@adequacy.main_adequacy_trace fullprog (λ x, x = 1)).
    2: { intros [? ?]. by intros (? & ? & ->). }
    intros ?. rewrite -fullprog_correct. apply main_proto_mono; eauto.
  Qed.
End Adequacy.
(*
Check @swap_pair_adequate.
Print Assumptions swap_pair_adequate.
*)
