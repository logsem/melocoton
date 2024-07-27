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

Import
  melocoton.c_lang.notation
  melocoton.c_lang.proofmode
  melocoton.c_interop.notation.

Context `{SI:indexT}.
Context `{!ffiG Σ}.

Definition get_raise_ml_spec (Ψ : protocol ML_lang.val Σ) : protocol ML_lang.val Σ :=
  !! (x:Z) f v e
    {{
      WP (rec: f v := e)%MLV #ML x at ⟨ ∅, Ψ ⟩
      {{ o, ⌜o = OExn (#ML (x + 1))⌝ }}
    }}
      "get_raise" with [ RecV f v e; #ML x ]
    {{ RET OExn (#ML(x + 2)); True }}.

Definition get_raise_code (f : expr) (x : expr) : expr :=
  let: "r" := Callback_exn (f, x) in
  if: *"r" = #0 then Val_int(#0) else
  let: "ret" := Int_val ( *("r" +ₗ #1) ) in
  Raise (Val_int ("ret" + #1)).

Definition get_raise_func : function :=
  Fun [BNamed "f"; BNamed "x"] (get_raise_code "f" "x").
Definition get_raise_prog : lang_prog C_lang := {[ "get_raise" := get_raise_func]}.

Lemma get_raise_correct Ψ :
  prims_proto Ψ ||- get_raise_prog :: wrap_proto (get_raise_ml_spec Ψ).
Proof.
  iIntros (fn ws Φ) "H". iNamed "H". iNamedProto "Hproto".
  iSplit; first done. iIntros (Φ'') "HΦ".
  iAssert (⌜length lvs = 2⌝)%I as %Hlen.
  { by iDestruct (big_sepL2_length with "Hsim") as %?. }
  destruct lvs as [|lv []]; try by (exfalso; eauto with lia); [].
  destruct l0; try by (exfalso; eauto with lia); []. clear Hlen.
  destruct ws as [|w []]; try by (exfalso; apply Forall2_length in Hrepr; eauto with lia); [].
  destruct l0; try by (exfalso; apply Forall2_length in Hrepr; eauto with lia); [].
  apply Forall2_cons_1 in Hrepr as [Hrepr1 Hrepr2].
  apply Forall2_cons_1 in Hrepr2 as [Hrepr2 _].
  cbn. iDestruct "Hsim" as "((%γ & -> & Hγ) & -> & _)".
  iAssert (Lint x ~~ #ML x) as "Hl"; first eauto.
  wp_call_direct.

  wp_apply (wp_callback_exn with "[$HGC $Hγ $Hl ProtoPre]");
  [done.. | |]; first iFrame.

  iIntros (θ' res is_exn ret lvret wret) "(HGC & Hres & Hlr & %Hrepr & H)".
  wp_pures. cbn. iDestruct "Hres" as "(Hres & Hret & _)".
  rewrite loc_add_0. wp_apply (wp_load with "Hres").
  iIntros "Hres"; wp_pures. case_bool_decide.
  { subst. cbn. iDestruct "H" as "%H". inversion H. }

  apply <-Z.eqb_neq in H. rewrite H.
  wp_pures. iDestruct "H" as "%Hret". inversion Hret.
  wp_apply (wp_load with "Hret"). iIntros "Hret".
  subst. cbn. iDestruct "Hlr" as "->". inversion Hrepr. cbn.

  wp_apply (wp_val2int with "HGC"); eauto; iIntros "HGC".
  wp_pures.

  wp_apply (wp_int2val with "HGC"); auto.
  iIntros (resv) "(HGC&%Hr)". cbn.

  wp_apply (wp_raise_prim); auto. iIntros "_".
  iApply "HΦ". iApply ("Return" $! _ _ (OExn (Lint _)) with "HGC [Cont]").
  - now iApply "Cont".
  - eauto.
  - iPureIntro. econstructor. rewrite -Z.add_assoc in Hr.
    now replace (1 + 1)%Z with 2%Z in Hr by eauto.
Qed.

End C_prog.

Section JustML.
Context `{SI:indexT}.
Context `{!ffiG Σ}.
Import
  melocoton.ml_lang.proofmode
  melocoton.ml_lang.notation.

  Definition raise_client : mlanguage.expr (lang_to_mlang ML_lang) :=
    (try: (extern: "get_raise" with ((λ: "x", raise: ("x" + #1)), #1))
    with: "v" => "v" + #1)%MLE.

  Lemma ML_prog_correct_axiomatic Ψ :
    ⊢ WP raise_client at ⟨∅, (get_raise_ml_spec Ψ)⟩
    {{ k, ⌜∃ x : Z, k = OVal #ML x ∧ x = 4⌝ }}.
  Proof.
    unfold raise_client. wp_pures. wp_extern.
    iModIntro. cbn. iSplit; first done. iExists _, _, _, _.
    iSplitR; first done.
    iSplitR.
    { iApply to_named. wp_rec. wp_pures; eauto. }
    iIntros "!> _".
    wp_pures. iApply (wp_try). wp_pures.
    iModIntro. wp_rec. wp_pures. eauto.
  Qed.

End JustML.

