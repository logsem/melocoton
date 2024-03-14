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

Definition add_one_ml_spec : protocol ML_lang.val Σ :=
  !! (x:Z)
    {{ True }}
      "add_one" with [ (#ML x) ]
    {{ RET (#ML(x + 1)); True }}.

Definition add_one_code (x : expr) : expr :=
  let: "r" := (call: &"val2int" with (x)) in
  (call: &"int2val" with ("r" + #1)).

Definition add_one_func : function := Fun [BNamed "x"] (add_one_code "x").
Definition add_one_prog : lang_prog C_lang := {[ "add_one" := add_one_func]}.

Lemma add_one_correct :
  prims_proto add_one_ml_spec ||- add_one_prog :: wrap_proto add_one_ml_spec.
Proof.
  iIntros (fn ws Φ) "H". iNamed "H". iNamedProto "Hproto".
  iSplit; first done. iIntros (Φ'') "HΦ".
  iAssert (⌜length lvs = 1⌝)%I as %Hlen.
  { by iDestruct (big_sepL2_length with "Hsim") as %?. }
  destruct lvs as [|lv []]; try by (exfalso; eauto with lia); []. clear Hlen.
  destruct ws as [|w []]; try by (exfalso; apply Forall2_length in Hrepr; eauto with lia); [].
  apply Forall2_cons_1 in Hrepr as [Hrepr _].
  cbn. iDestruct "Hsim" as "[-> _]".
  wp_call_direct.

  inversion Hrepr; subst.
  wp_apply (wp_val2int with "HGC"); auto.
  iIntros "HGC". wp_pures.

  wp_apply (wp_int2val with "HGC"); auto.
  iIntros (w) "(HGC&Hr)".

  iApply "HΦ". iApply ("Return" with "HGC [Cont] []"); eauto.
  - by iApply "Cont".
  - cbn. done.
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
    {[ "add_one" := FunType [ TNat ] TNat ]}.

  Lemma swap_pair_well_typed Δ : ⊢ ⟦ program_type_ctx ⟧ₚ* ⟨∅, add_one_ml_spec⟩ Δ.
  Proof.
    iIntros (s vv Φ) "!> (%ats&%rt&%Heq&Hargs&Htok&HCont)".
    wp_extern. iModIntro. unfold program_type_ctx in Heq.
    apply lookup_singleton_Some in Heq as (<-&Heq). simplify_eq.
    iPoseProof (big_sepL2_length with "Hargs") as "%Heq".
    destruct vv as [|v [|??]]; cbn in Heq; try lia.
    cbn. iDestruct "Hargs" as "((%n&->)&_)".
    iSplit; first done. iExists n. iSplit; first done. iSplit; first done.
    iIntros "!> _". wp_pures. iModIntro. iApply ("HCont" with "[-Htok] Htok").
    iExists _. eauto.
  Qed.
  End LogRel.

Definition add_one_client : mlanguage.expr (lang_to_mlang ML_lang) :=
  (Extern "add_one" [ Val (#1)%MLE ]).

Lemma ML_prog_correct_axiomatic :
  ⊢ WP add_one_client at ⟨∅, add_one_ml_spec⟩ {{ v, ⌜v = #2%Z⌝}}.
Proof.
  unfold add_one_client. wp_pures.
  wp_extern.
  iModIntro. cbn. iSplit; first done. iExists _.
  do 2 (iSplitR; first done). iIntros "!> _".
  wp_pures. iModIntro. iPureIntro. done.
Qed.

End JustML.

Local Existing Instance ordinals.ordI.

Definition fullprog : mlang_prog combined_lang :=
  combined_prog add_one_client add_one_prog.

Lemma add_one_adequate :
  umrel.trace (mlanguage.prim_step fullprog) (LkCall "main" [], adequacy.σ_init)
    (λ '(e, σ), mlanguage.to_val e = Some (code_int 2)).
Proof.
  eapply umrel_upclosed.
  { eapply combined_adequacy_trace. intros Σ Hffi. split_and!.
    3: {iIntros "_". admit. (* iApply ML_prog_correct_axiomatic. *) }
    3: apply add_one_correct.
    { iIntros (? Hn ?) "(% & H)". iDestruct "H" as (? ? ->) "H".
      exfalso. set_solver. }
    { set_solver. } }
  { intros [?] (? & -> & ?). do 2 f_equal. admit. }
Admitted.
(* Qed. *)

