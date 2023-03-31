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
Context `{SI:indexT}.
Context `{!heapG_C Σ, !invG Σ}.

Definition is_odd_proto : protocol val Σ := (λ fn (vs: list val) Φ,
  ⌜fn = "is_odd"⌝ ∗ ∃ (x:Z), ⌜vs = [ #x ] ∧ (0 ≤ x)%Z⌝ ∗
  Φ (# (Z.odd x)))%I.

Definition is_even_proto : protocol val Σ := (λ fn vs Φ,
  ⌜fn = "is_even"⌝ ∗ ∃ (x:Z), ⌜vs = [ #x ] ∧ (0 ≤ x)%Z⌝ ∗
  Φ (# (Z.even x)))%I.

Lemma wp_is_even (x:Z) E :
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

Lemma is_even_correct E : is_odd_proto ||- is_even_prog @ E :: is_even_proto.
Proof.
  unfold progwp, is_even_proto.
  iIntros (? ? ?) "[-> H]". iDestruct "H" as (? [-> ?]) "H".
  rewrite lookup_insert. do 2 (iExists _; iSplit; first done). iNext.
  iApply wp_wand; first by iApply wp_is_even. by iIntros (? ->).
Qed.

Lemma wp_is_odd (x:Z) E :
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

Lemma is_odd_correct E : is_even_proto ||- is_odd_prog @ E :: is_odd_proto.
Proof.
  unfold progwp, is_odd_proto.
  iIntros (? ? ?) "[-> H]". iDestruct "H" as (? [-> ?]) "H".
  rewrite lookup_insert. do 2 (iExists _; iSplit; first done). iNext.
  iApply wp_wand; first by iApply wp_is_odd. by iIntros (? ->).
Qed.

End specs.

From melocoton.lang_to_mlang Require Import weakestpre.
From melocoton.linking Require Import lang weakestpre.
From melocoton.c_lang Require Import mlang_instantiation.
From melocoton.mlanguage Require Import weakestpre.

Section linking.
Context `{SI:indexT}.
Context `{!heapG_C Σ, !invG Σ}.
Context `{!linkG Σ}.

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
  - apply lang_to_mlang_correct. rewrite proto_on_refines. apply is_odd_correct.
  - apply lang_to_mlang_correct. rewrite proto_on_refines. apply is_even_correct.
  - iIntros (? ? ?) "[% [-> _]]". exfalso. naive_solver.
  - iIntros (? ? ?) "[% [-> _]]". exfalso. naive_solver.
Qed.

(* The full program implements both is_even and is_odd, without making external calls *)
Lemma fullprog_correct E : ⊥ |- fullprog @ E :: is_even_proto ⊔ is_odd_proto.
Proof.
  intros. eapply link_correct; first typeclasses eauto; apply lang_to_mlang_correct.
  - apply is_even_correct.
  - apply is_odd_correct.
Qed.

(* From this we can derive that calling is_even/is_odd in fullprog satisfies
   their respective spec. *)
Lemma is_even_linked_spec (x:Z) E :
  (0 ≤ x)%Z →
  {{{ link_in_state _ _ Boundary }}}
    LkSE (Link.ExprCall "is_even" [ #x ]) @ ⟪fullprog, ⊥⟫; E
  {{{ RET #(Z.even x); link_in_state _ _ Boundary }}}.
Proof.
  iIntros (Hx Φ) "Hlkst HΦ".
  iApply (wp_internal_call_at_boundary fullprog with "[$Hlkst]"); try done.
  { iApply fullprog_correct. iLeft. iSplit; first done.
    instantiate (1 := (λ y, ⌜y = #(Z.even x)⌝)%I). eauto. }
  iNext. iIntros (? ->) "?". cbn. iApply (wp_value ⟪fullprog, ⊥⟫); eauto.
  by iApply "HΦ".
Qed.

Lemma is_odd_linked_spec (x:Z) E :
  (0 ≤ x)%Z →
  {{{ link_in_state _ _ Boundary }}}
    LkSE (Link.ExprCall "is_odd" [ #x ]) @ ⟪fullprog, ⊥⟫; E
  {{{ RET #(Z.odd x); link_in_state _ _ Boundary }}}.
Proof.
  iIntros (Hx Φ) "Hlkst HΦ".
  iApply (wp_internal_call_at_boundary fullprog with "[$Hlkst]"); try done.
  { iApply fullprog_correct. iRight. iSplit; first done.
    instantiate (1 := (λ y, ⌜y = #(Z.odd x)⌝)%I). eauto. }
  iNext. iIntros (? ->) "?". cbn. iApply (wp_value ⟪fullprog, ⊥⟫); eauto.
  by iApply "HΦ".
Qed.

End linking.
