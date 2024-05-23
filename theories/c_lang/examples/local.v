From iris.proofmode   Require Import coq_tactics reduction spec_patterns.
From iris.proofmode   Require Export tactics.
From iris.prelude     Require Import options.
From melocoton        Require Import named_props.
From melocoton.c_lang Require Import lang notation proofmode.

Context `{SI:indexT}.
Context `{!heapG_C Σ, !invG Σ}.

Tactic Notation "wp_allocframe" ident(fp) uconstr(Hfp) :=
  wp_pures;
  wp_apply (wp_allocframe);
  iIntros (fp) "Hfp"; unfold allocate_frame; cbn -[array]; wp_pures.

Section One.

  Definition addr : expr :=
    &: "e".

  Definition arg_prog : lang_prog C_lang :=
    {[ "addr" := Fun [BNamed "e"] addr ]}.

  Definition arg_prog_spec : protocol val Σ :=
    !! e {{ True }} "addr" with [e] {{ (l : loc), RET(#C l); True }}.

  Lemma arg_correct:
    ||- arg_prog :: arg_prog_spec.
  Proof.
    iIntros (ψext x lvs ϕ) "H". iNamed "H". iSplit; first done.
    iIntros (Φ') "HΦ". iNamed "H".

    wp_allocframe fp "Hfp".
    wp_apply (wp_free_array with "Hfp").
    iIntros "_". wp_pures.
    iModIntro. iApply "HΦ". by iApply "Cont".
  Qed.

End One.

Section Two.

  Definition id : expr :=
    let: "_" := &: "e" in
    "e".

  Definition id_prog : lang_prog C_lang :=
    {[ "id" := Fun [BNamed "e"] id ]}.

  Definition id_spec : protocol val Σ :=
    !! e {{ True }} "id" with [e] {{ RET(e); True }}.

  Lemma id_correct:
    ||- id_prog :: id_spec.
  Proof.
    iIntros (ψext x lvs ϕ) "H". iNamed "H". iSplit; first done.
    iIntros (Φ') "HΦ". iNamed "H".
    wp_call_direct.
    wp_allocframe fp "Hfp".
  Admitted.

End Two.

Section Three.

  Definition incr : expr :=
    "p" <- *"p" + #C 1.

  (* Times two plus one *)
  Definition ttpo : expr :=
    let: "e2" := "e" in
    call: &"incr" with (&: "e");;
    "e2" + "e".

  Definition ttpo_prog : lang_prog C_lang :=
    {[
      "incr" := Fun [BNamed "p"] incr;
      "ttpo" := Fun [BNamed "e"] ttpo
    ]}.

  Definition ttpo_spec : protocol val Σ :=
    !! e (n : Z) {{ ⌜e = #C n⌝ }} "ttpo" with [e] {{ RET(#C (n + n + 1)); True }}.

  Lemma ttpo_correct:
    ||- ttpo_prog :: ttpo_spec.
  Proof.
    iIntros (ψext x lvs ϕ) "H". iNamed "H". iSplit; first done.
    iIntros (Φ') "HΦ". iNamed "H".
    wp_call_direct.
    wp_allocframe fp "Hfp".
    wp_apply (wp_load).
  Admitted.

End Three.
