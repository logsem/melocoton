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

Definition is_odd_proto : protocol val Σ :=
  !! (x:Z)
  {{ "%" ∷ ⌜(0 ≤ x)%Z⌝ }}
    "is_odd" with [ #x ]
  {{ RET #(Z.odd x); True }}.

Definition is_even_proto : protocol val Σ :=
  !! (x:Z)
  {{ "%" ∷ ⌜(0 ≤ x)%Z⌝ }}
    "is_even" with [ #x ]
  {{ RET #(Z.even x); True }}.

Lemma wp_is_even (x:Z) :
  (0 ≤ x)%Z →
  ⊢ WP subst "x" (#x) (is_even_code "x") at ⟨is_even_prog, is_odd_proto⟩
      {{ λ v, ⌜v = OVal #(Z.even x)⌝ }}.
Proof.
  iIntros (?). iStartProof.
  rewrite /is_even_code /=. cbn; simplify_map_eq.
  wp_pures. case_bool_decide as Hx; wp_if.
  { by inversion Hx. }
  wp_pures. case_bool_decide as Hx'; wp_if.
  { by inversion Hx'. }
  wp_pures. wp_extern. iModIntro. cbn.
  rewrite /is_odd_proto /=. iSplitR; first done.
  iExists _. iSplit; first done. iSplitR.
  { iPureIntro. lia. }
  iIntros "!> _". wp_pures. iPureIntro. f_equal. rewrite Z.sub_1_r Z.odd_pred //.
Qed.

Lemma is_even_correct : is_odd_proto ||- is_even_prog :: is_even_proto.
Proof.
  unfold progwp, is_even_proto.
  iIntros (? ? ?) "H". iNamedProto "H". iSplit; first done.
  iIntros (?) "Hcont". wp_call_direct.
  iApply wp_wand; first by iApply wp_is_even. iIntros (? ->).
  iApply "Hcont". by iApply "Cont".
Qed.

Lemma wp_is_odd (x:Z) :
  (0 ≤ x)%Z →
  ⊢ WP subst "x" (#x) (is_odd_code "x") at ⟨is_odd_prog, is_even_proto⟩
      {{ λ v, ⌜v = OVal #(Z.odd x)⌝ }}.
Proof.
  iIntros (?). iStartProof.
  rewrite /is_even_code /=. cbn; simplify_map_eq.
  wp_pures. case_bool_decide as Hx; wp_if.
  { by inversion Hx. }
  wp_pures. case_bool_decide as Hx'; wp_if.
  { by inversion Hx'. }
  wp_pures. wp_extern. iModIntro. cbn.
  rewrite /is_odd_proto /=. iSplitR; first done.
  iExists _. iSplit; first done. iSplitR.
  { iPureIntro. lia. }
  iIntros "!> _". wp_pures. iPureIntro. f_equal.
  rewrite Z.sub_1_r Z.even_pred //.
Qed.

Lemma is_odd_correct : is_even_proto ||- is_odd_prog :: is_odd_proto.
Proof.
  unfold progwp, is_odd_proto.
  iIntros (? ? ?) "H". iNamedProto "H". iSplit; first done.
  iIntros (?) "Hcont". wp_call_direct.
  iApply wp_wand; first by iApply wp_is_odd. iIntros (? ->). 
  iApply "Hcont". by iApply "Cont".
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

(* The full program implements both is_even and is_odd, without making external calls *)
Lemma fullprog_correct : ⊥ |- fullprog :: is_even_proto ⊔ is_odd_proto.
Proof.
  intros. eapply link_close_correct; [set_solver|..].
  - apply lang_to_mlang_correct, is_even_correct.
  - apply lang_to_mlang_correct, is_odd_correct.
Qed.

(* From this we can derive that calling is_even/is_odd in fullprog satisfies
   their respective spec. *)
Lemma is_even_linked_spec (x:Z) :
  (0 ≤ x)%Z →
  {{{ link_in_state _ _ Boundary }}}
    LkSE (Link.ExprCall "is_even" [ #x ]) at ⟪fullprog, ⊥⟫
  {{{ RET #(Z.even x); link_in_state _ _ Boundary }}}.
Proof.
  iIntros (Hx Φ) "Hlkst HΦ".
  iApply (wp_internal_call_at_boundary fullprog with "[$Hlkst]").
  - iApply fullprog_correct. iLeft. iSplit; first done.
    instantiate (1 := (λ y, ⌜y = OVal #(Z.even x)⌝)%I). eauto.
  - cbn. iIntros "!>" (?) "[-> ?]". by iApply "HΦ".
Qed.

Lemma is_odd_linked_spec (x:Z) :
  (0 ≤ x)%Z →
  {{{ link_in_state _ _ Boundary }}}
    LkSE (Link.ExprCall "is_odd" [ #x ]) at ⟪fullprog, ⊥⟫
  {{{ RET #(Z.odd x); link_in_state _ _ Boundary }}}.
Proof.
  iIntros (Hx Φ) "Hlkst HΦ".
  iApply (wp_internal_call_at_boundary fullprog with "[$Hlkst]").
  - iApply fullprog_correct. iRight. iSplit; first done.
    instantiate (1 := (λ y, ⌜y = OVal #(Z.odd x)⌝)%I). eauto.
  - cbn. iIntros "!>" (?) "[-> ?]". by iApply "HΦ".
Qed.

End linking.
