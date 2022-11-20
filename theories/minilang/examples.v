From iris.proofmode Require Import proofmode.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import linking linking_wp.
From melocoton.minilang Require Import lang primitive_laws.
From iris.prelude Require Import options.

Import Mini.

Definition code1 : list instr := [
  Register 1;
  Const 42; Write 1;
  Register 2;
  Const 12; Write 2;
  Call "f" 0;
  Read 1; Assert 42;
  Read 2; Assert 13;
  Read 3
].

Definition code2 : list instr := [
  Const 13; Write 2;
  Register 3
].

Section specs.
Context `{!minilangGS hlc Σ}.

Definition penv1 : prog_environ mini_lang Σ := {|
  penv_prog := {[ "main" := E code1 ]};
  penv_proto := (λ fn vs Φ, ⌜fn = "f"⌝ ∗ ∃ n,
    ACC n ∗ 2 ↦ 12 ∗
    AVAILABLE (⊤ ∖ {[ Pos.of_nat 1 ]} ∖ {[ Pos.of_nat 2 ]}) ∗
    (∀ m, ACC m ∗ 2 ↦ 13 ∗ REGISTERED 3 ∗
          AVAILABLE (⊤ ∖ {[ Pos.of_nat 1 ]} ∖ {[ Pos.of_nat 2 ]} ∖ {[ Pos.of_nat 3 ]})
       -∗ Φ ()))%I;
|}.

Definition penv2 : prog_environ mini_lang Σ := {|
  penv_prog := {[ "f" := E code2 ]};
  penv_proto := (λ _ _ _, False)%I
|}.

Ltac wp_const H :=
  wp_bind; iApply (wp_const with H); iNext; iIntros H.

Ltac wp_assert H :=
  wp_bind; iApply (wp_assert with H); [done | iNext; iIntros H].

Lemma code1_spec n EE :
  {{{ ACC n ∗ AVAILABLE ⊤ }}}
    E code1 @ penv1; EE
  {{{ RET (); ∃ m, ACC m }}}.
Proof.
  rewrite /code1. iIntros (Φ) "[Ha Hav] HΦ".
  wp_bind. iApply (wp_register with "Hav"); first done.
  iIntros "!> (H1 & Hreg0 & Hav)".
  wp_const "Ha".
  wp_bind. iApply (wp_write with "[$H1 $Ha]").
  iIntros "!> [H1 Ha]".
  wp_bind. iApply (wp_register with "Hav"); first done.
  iIntros "!> (H2 & Hreg2 & Hav)".
  wp_const "Ha".
  wp_bind. iApply (wp_write with "[$H2 $Ha]").
  iIntros "!> [H2 Ha]".
  wp_bind. iApply wp_extern; first by set_solver.
  simpl. iSplitR; first done. iExists _. iFrame "Ha H2 Hav".
  iIntros (m) "(Ha & H2 & Hreg3 & Hav)".
  wp_bind. iApply (wp_read with "[$H1 $Ha]").
  iIntros "!> [H1 Ha]".
  wp_assert "Ha".
  wp_bind. iApply (wp_read with "[$H2 $Ha]").
  iIntros "!> [H2 Ha]".
  wp_assert "Ha".
  wp_bind. iApply (wp_read_registered with "[$Hreg3 $Ha]").
  iIntros "!> [%k Ha]".
  iApply wp_value'. iApply "HΦ". iExists _. by iFrame.
Qed.

Lemma code2_spec n m EE :
  {{{ ACC n ∗ 2 ↦ m ∗ AVAILABLE (⊤ ∖ {[ Pos.of_nat 1 ]} ∖ {[ Pos.of_nat 2 ]}) }}}
    E code2 @ penv2; EE
  {{{ RET (); ∃ k, ACC k ∗ 2 ↦ 13 ∗ REGISTERED 3 ∗
              AVAILABLE (⊤ ∖ {[ Pos.of_nat 1 ]} ∖ {[ Pos.of_nat 2 ]} ∖ {[ Pos.of_nat 3 ]}) }}}.
Proof.
  rewrite /code2. iIntros (Φ) "(Ha & H2 & Hav) HΦ".
  wp_const "Ha".
  wp_bind. iApply (wp_write with "[$H2 $Ha]").
  iIntros "!> [H2 Ha]".
  wp_bind. iApply (wp_register with "Hav"); first done.
  iIntros "!> (H3 & Hreg3 & Hav)".
  iApply wp_value'. iApply "HΦ". iExists _. by iFrame.
Qed.
End specs.

Section linking.
Context `{!minilangGS hlc Σ}.
Context `{!linkGS Σ}.

Definition penv : prog_environ (link_lang mini_lang mini_lang) Σ := {|
  penv_prog := {[ "main" := inl (E code1); "f" := inr (E code2) ]};
  penv_proto := (λ _ _ _, False)%I;
|}.

Instance penv_is_link : is_link_environ penv1 penv2 penv.
Proof.
  constructor.
  { set_solver. }
  { rewrite /= !fmap_insert !fmap_empty // -insert_union_l.
    rewrite left_id_L //. }
  { iIntros (fn func vs Φ EE Hfn) "(-> & HT)". simpl in Hfn. simplify_map_eq.
    iDestruct "HT" as (n) "(Ha & H2 & Hav & HΦ)". iExists _. iSplitR; first done.
    iNext. iIntros "_". iApply (wp_wand with "[-]").
    { iApply (code2_spec with "[$Ha $H2 $Hav]"). iNext. iIntros "(%k & ? & ? & ?)".
      iApply "HΦ". iFrame. }
    iIntros (?) "?". iFrame. }
  { iIntros (? ? ? ? ? ?) "[]". }
  { iIntros (? ? ? ? ?) "(-> & ?)". simpl in *. simplify_map_eq. }
  { iIntros (? ? ? ? ?) "?". by simpl in *. }
Qed.

Lemma main_spec n :
  {{{ ACC n ∗ AVAILABLE ⊤ ∗ link_in_state _ _ Boundary }}}
    LkSE (Link.ExprCall "main" []) @ penv; ⊤
  {{{ RET (); ∃ m, ACC m ∗ link_in_state _ _ Boundary }}}.
Proof.
  iIntros (Φ) "(Ha & Hav & Hlkst) HΦ".
  iApply wp_link_internal_call; first done. iNext.
  iApply (wp_link_run_function1 with "Hlkst"); first done.
  iIntros "!> Hlkst _".
  iApply (@wp_wand with "[-HΦ]").
  { iApply (wp_link_run1 with "Hlkst").
    iApply (code1_spec _ _ (λ _, (∃ m, ACC m) ∗ True)%I with "[$Ha $Hav]").
    iNext. iIntros "H". iFrame. }
  iIntros ([]) "(? & ?)". iApply "HΦ". iFrame.
Qed.

End linking.
