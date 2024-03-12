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


Definition swap_variant_code (x : expr) : expr :=
  let: "v" := malloc (#1) in
  ("v" +ₗ #0 <- (call: &"readfield" with ("x", Val #0))) ;;
  (call: &"registerroot" with (Var "v" +ₗ #0)) ;;
  let: "t" := (call: &"read_tag" with (x)) in
  let: "r" := (call: &"alloc" with (!"t", #1)) in
  (call: &"modify" with (Var "r", Val #0, * (Var "v" +ₗ #0))) ;;
  (call: &"unregisterroot" with (Var "v" +ₗ #0)) ;;
  (free ("v", #1)) ;;
  "r".

Definition swap_variant_func : function := Fun [BNamed "x"] (swap_variant_code "x").
Definition swap_variant_prog : lang_prog C_lang := {[ "swap_variant" := swap_variant_func ]}.

Definition swap_sum v :=
  match v with
  | InjLV v => Some (InjRV v)
  | InjRV v => Some (InjLV v)
  | _       => None
  end.

Definition swap_variant_ml_spec : protocol ML_lang.val Σ := (
  λ s l Φ, ∃ v r, ⌜s = "swap_variant"⌝ ∗
                  ⌜l = [ v%MLV ]⌝ ∗
                  ⌜swap_sum v = Some r⌝∗
                  Φ r%MLV
)%I.

Lemma swap_pair_correct :
  prims_proto swap_variant_ml_spec ||- swap_variant_prog :: wrap_proto swap_variant_ml_spec.
Proof.
  iIntros (fn ws Φ) "H". iNamed "H".
  iDestruct "Hproto" as (v r) "(->&->&Hs&Hψ)".
  iSplit; first done. iIntros (Φ'') "HΦ".
  iAssert (⌜length lvs = 1⌝)%I as %Hlen.
  { by iDestruct (big_sepL2_length with "Hsim") as %?. }
  destruct lvs as [|lv []]; try by (exfalso; eauto with lia); []. clear Hlen.
  destruct ws as [|w []]; try by (exfalso; apply Forall2_length in Hrepr; eauto with lia); [].
  apply Forall2_cons_1 in Hrepr as [Hrepr _].
  cbn. iDestruct "Hsim" as "(Hsim&_)".
  wp_call_direct.

  wp_alloc rr as "H"; first done.
  change (Z.to_nat 1) with 1. cbn. iDestruct "H" as "(H&_)". destruct rr as [rr].
  wp_pures.

  unfold swap_sum. destruct v; iDestruct "Hs" as "%Hptpair";
    try done; simplify_eq.
  - iDestruct "Hsim" as (γ lv0 ->) "H'".
  iUnfold swap_sum in "Hs".

  (* readfield 1 *)
  wp_apply (wp_readfield with "[$HGC $Hptpair]"); [done..|].
  iIntros (v' wlv) "(HGC & _ & %Heq & %Hrepr1)".
  change (Z.to_nat 0) with 0 in Heq. cbn in *. symmetry in Heq. simplify_eq.
  wp_apply (wp_store with "H"). iIntros "H". wp_pures.

  (* registerroot 1 *)
  wp_apply (wp_registerroot with "[$HGC $H]"); [done..|].
  iIntros "(HGC & H1r)". wp_pures.

  (* read_tag(w) *)
  wp_apply (wp_read_tag with "[$HGC ]"); [done..| |].
  { by iDestruct "Hptpair" as "[??]". }
  iIntros "[HGC _]". wp_pures.

  (* alloc(!"t", #1) *)
  wp_apply (wp_alloc TagInjRV with "HGC"); try done.
  iIntros (θ' γnew wnew) "(HGC & Hnew & %Hreprnew)". wp_pures.
  change (Z.to_nat 1) with 1. cbn [repeat].

  (* load from root *)
  wp_apply (load_from_root with "[HGC H1r]"); first iFrame.
  iIntros (wlv') "(Hr&HGC&%Hrepr')".

  (* modify *)
  wp_apply (wp_modify with "[$HGC $Hnew]"); [done..|].
  iIntros "(HGC & Hnew)". change (Z.to_nat 0) with 0. cbn.
  wp_pures.

  (* unregisterroot 1 *)
  wp_apply (wp_unregisterroot with "[$HGC $Hr]"); [done..|].
  iIntros (wlv'') "(HGC & H & %Hrepr'')".
  repr_lval_inj. wp_pures.

  (* free *)
  iAssert ((Loc rr) ↦C∗ [Some wlv'])%I with "[H]" as "Hrr".
  1: cbn; iFrame.
  wp_apply (wp_free_array' with "Hrr"); first done. iIntros "_".
  wp_pures.

  (* Finish, convert the new points-to to an immutable pointsto *)
  iMod (freeze_to_immut γnew _ θ' with "[$]") as "(HGC&#Hnew)".

  iModIntro. iApply "HΦ". iApply ("Cont" with "HGC Hψ [] []").
  - cbn. do 2 iExists _. iFrame "Hnew Hlv0". done.
  - done.
Qed.

End C_prog.

Section JustML.
Context `{SI:indexT}.
Context `{!ffiG Σ}.
Import melocoton.ml_lang.proofmode.

  Section LogRel.
  Import logrel typing fundamental.
  Context `{!logrelG Σ}.
  Context (A B : type).

  Definition program_type_ctx : program_env := 
    {[ "swap_variant" := FunType [ TSum A B ] (TSum B A) ]}.

  Lemma swap_pair_well_typed Δ : ⊢ ⟦ program_type_ctx ⟧ₚ* ⟨∅, swap_variant_ml_spec⟩ Δ.
  Proof.
    iIntros (s vv Φ) "!> (%ats&%rt&%Heq&Hargs&Htok&HCont)".
    wp_extern. iModIntro. unfold program_type_ctx in Heq.
    apply lookup_singleton_Some in Heq as (<-&Heq). simplify_eq.
    iPoseProof (big_sepL2_length with "Hargs") as "%Heq".
    destruct vv as [|v [|??]]; cbn in Heq; try lia.
    cbn. iDestruct "Hargs" as "((%w&&->&Hw1)&_)".
    iExists _. iSplit; first done. iSplit; first done.
    wp_pures. iModIntro. iApply ("HCont" with "[-Htok] Htok").
    iExists _, _. iSplit; first done. iFrame.
  Qed.
  End LogRel.

Definition swap_pair_client : mlanguage.expr (lang_to_mlang ML_lang) :=
  (Extern "swap_variant" [ (InjL #1)%MLE ]).

Lemma ML_prog_correct_axiomatic :
  ⊢ WP swap_pair_client at ⟨∅, swap_pair_ml_spec⟩ {{ v, ⌜∃ x : Z, v = #x ∧ x = 1⌝}}.
Proof.
  unfold swap_pair_client. wp_pures.
  wp_extern.
  iModIntro. cbn. do 2 iExists _.
  do 2 (iSplitR; first done).
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
    { iIntros (? Hn ?) "(% & H)". iDestruct "H" as (? ? ->) "H".
      exfalso. set_solver. }
    { set_solver. } }
  { by intros [? ?] (? & ? & ->). }
Qed.
(*
Check @swap_pair_adequate.
Print Assumptions swap_pair_adequate.
*
