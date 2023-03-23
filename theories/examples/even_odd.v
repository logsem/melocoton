From Coq Require Import Lia.
From iris.proofmode Require Import proofmode.
From melocoton.c_lang Require Import notation proofmode.
From melocoton.mlanguage Require Import progenv.
From melocoton.language Require Import weakestpre.
From iris.prelude Require Import options.

Definition is_even_code (x : string) : C_lang.expr :=
  if: x = #0 then #true
  else if: x = #1 then #false
  else call: &"is_odd" with (x - #1).

Definition is_even_prog : lang_prog C_lang :=
  {[ "is_even" := Fun [BNamed "x"] (is_even_code "x") ]}.

Definition is_odd_code (x : string) : C_lang.expr :=
  if: x = #0 then #false
  else if: x = #1 then #true
  else call: &"is_even" with (x - #1).

Definition is_odd_prog : lang_prog C_lang :=
  {[ "is_odd" := Fun [BNamed "x"] (is_odd_code "x") ]}.


Section specs.
Context `{!heapGS_C Σ, !invGS_gen hlc Σ}.

Definition is_odd_proto : protocol val Σ := (λ fn (vs: list val) Φ,
  ⌜fn = "is_odd"⌝ ∗ ∃ (x:Z), ⌜vs = [ #x ] ∧ (0 ≤ x)%Z⌝ ∗
  Φ (# (Z.odd x)))%I.

Definition is_even_proto : protocol val Σ := (λ fn vs Φ,
  ⌜fn = "is_even"⌝ ∗ ∃ (x:Z), ⌜vs = [ #x ] ∧ (0 ≤ x)%Z⌝ ∗
  Φ (# (Z.even x)))%I.

Lemma is_even_correct (x:Z) E :
  (0 ≤ x)%Z →
  ⊢ WP subst "x" (#x) (is_even_code "x") @ ⟨is_even_prog, is_odd_proto⟩; E
      {{ λ v, ⌜v = #(Z.even x)⌝ }}.
Proof.
  iIntros (?). iStartProof.
  rewrite /is_even_code /=. cbn; simplify_map_eq.
  wp_pures. case_bool_decide as Hx; wp_if.
  { by inversion Hx. }
  wp_pures. case_bool_decide as Hx'; wp_if.
  { by inversion Hx'. }
  wp_pures. wp_extern. iModIntro. cbn.
  rewrite /is_odd_proto /=. iSplitR; first done.
  iExists _. iSplitR.
  { iPureIntro. split; first done.
    assert (x ≠ 0). { intro. apply Hx. by f_equal. }
    lia. }
  wp_pures. iPureIntro. f_equal. rewrite Z.sub_1_r Z.odd_pred //.
Qed.

Lemma is_even_refines E : is_even_proto ⊑ prog_proto E is_even_prog is_odd_proto.
Proof.
  unfold prog_proto, is_even_proto.
  iIntros (? ? ?) "[-> H]". iDestruct "H" as (? [-> ?]) "H".
  rewrite lookup_insert. iExists _. iSplit; first done. iNext.
  iApply wp_wand; first by iApply is_even_correct. by iIntros (? ->).
Qed.

Lemma is_odd_correct (x:Z) E :
  (0 ≤ x)%Z →
  ⊢ WP subst "x" (#x) (is_odd_code "x") @ ⟨is_odd_prog, is_even_proto⟩; E
      {{ λ v, ⌜v = #(Z.odd x)⌝ }}.
Proof.
  iIntros (?). iStartProof.
  rewrite /is_even_code /=. cbn; simplify_map_eq.
  wp_pures. case_bool_decide as Hx; wp_if.
  { by inversion Hx. }
  wp_pures. case_bool_decide as Hx'; wp_if.
  { by inversion Hx'. }
  wp_pures. wp_extern. iModIntro. cbn.
  rewrite /is_odd_proto /=. iSplitR; first done.
  iExists _. iSplitR.
  { iPureIntro. split; first done.
    assert (x ≠ 0). { intro. apply Hx. by f_equal. }
    lia. }
  wp_pures. iPureIntro. f_equal. rewrite Z.sub_1_r Z.even_pred //.
Qed.

Lemma is_odd_refines E : is_odd_proto ⊑ prog_proto E is_odd_prog is_even_proto.
Proof.
  unfold prog_proto, is_odd_proto.
  iIntros (? ? ?) "[-> H]". iDestruct "H" as (? [-> ?]) "H".
  rewrite lookup_insert. iExists _. iSplit; first done. iNext.
  iApply wp_wand; first by iApply is_odd_correct. by iIntros (? ->).
Qed.

End specs.

From melocoton.lang_to_mlang Require Import weakestpre.
From melocoton.linking Require Import lang weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.c_lang Require Import mlang_instantiation.

Section linking.
Context `{!heapGS_C Σ, !invGS_gen hlc Σ}.
Context `{!linkGS Σ}.

Definition fullprog : mlang_prog (link_lang C_mlang C_mlang) :=
  link_prog C_mlang C_mlang is_even_prog is_odd_prog.

Instance can_link_even_odd :
  can_link C_mlang C_mlang
    is_even_prog is_odd_proto
    is_odd_prog  is_even_proto
    ⊥. (* there are no external calls left after linking *)
Proof.
  constructor; intros.
  - set_solver.
  - rewrite proto_on_refines is_odd_refines lang_to_mlang_refines //.
  - rewrite proto_on_refines is_even_refines lang_to_mlang_refines //.
  - iIntros (? ? ?) "[% [-> _]]". exfalso. naive_solver.
  - iIntros (? ? ?) "[% [-> _]]". exfalso. naive_solver.
Qed.

(* The full program implements both is_even and is_odd, without making external calls *)
Lemma fullprog_refines_even_odd E :
  is_even_proto ⊔ is_odd_proto ⊑ mprog_proto E fullprog ⊥.
Proof.
  rewrite -link_refines. apply proto_join_mono.
  - rewrite is_even_refines lang_to_mlang_refines //.
  - rewrite is_odd_refines lang_to_mlang_refines //.
Qed.

(* TODO: could those be derived more directly? *)
Lemma is_even_linked_spec (x:Z) E :
  (0 ≤ x)%Z →
  {{{ link_in_state _ _ Boundary }}}
    LkSE (Link.ExprCall "is_even" [ #x ]) @ ⟪fullprog, ⊥⟫; E
  {{{ RET #(Z.even x); link_in_state _ _ Boundary }}}.
Proof.
  iIntros (Hx Φ) "Hlkst HΦ".
  iApply wp_link_internal_call; first done.
  iIntros "!>". iApply (wp_link_run_function1 with "Hlkst"); first done.
  iIntros "!> Hlkst _".
  iApply (wp_link_run1' with "Hlkst").
  { iApply wp_wand.
    2: { iIntros (?) "H". by iSplitL; [by iApply "H"|]. }
    iApply wp_lang_to_mlang. by iApply is_even_correct. }
  { iIntros (?) "[-> ?]". by iApply "HΦ". }
Qed.

Lemma is_odd_linked_spec (x:Z) E :
  (0 ≤ x)%Z →
  {{{ link_in_state _ _ Boundary }}}
    LkSE (Link.ExprCall "is_odd" [ #x ]) @ ⟪fullprog, ⊥⟫; E
  {{{ RET #(Z.odd x); link_in_state _ _ Boundary }}}.
Proof.
  iIntros (Hx Φ) "Hlkst HΦ".
  iApply wp_link_internal_call; first done.
  iIntros "!>". iApply (wp_link_run_function2 with "Hlkst"); first done.
  iIntros "!> Hlkst _".
  iApply (wp_link_run2' with "Hlkst").
  { iApply wp_wand.
    2: { iIntros (?) "H". by iSplitL; [by iApply "H"|]. }
    iApply wp_lang_to_mlang. by iApply is_odd_correct. }
  iIntros (?) "[-> ?]". by iApply "HΦ".
Qed.

End linking.
