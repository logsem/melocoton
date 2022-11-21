From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang notation.
From melocoton.c_toy_lang.melocoton Require Import proofmode primitive_laws.
From melocoton.language Require Import weakestpre.
From iris.prelude Require Import options.

Definition is_even_code (x : string) : C_lang.expr :=
  if: x = #0 then #true
  else if: x = #1 then #false
  else call: &"is_odd" with (x - #1).

Definition is_even_func : C_lang.function :=
  Fun [BNamed "x"] (is_even_code "x").

Definition is_odd_code (x : string) : C_lang.expr :=
  if: x = #0 then #false
  else if: x = #1 then #true
  else call: &"is_even" with (x - #1).

Definition is_odd_func : C_lang.function :=
  Fun [BNamed "x"] (is_odd_code "x").


Section specs.
Context `{!heapGS_gen hlc Σ}.

Definition is_odd_proto fn (vs: list val) Φ : iProp Σ :=
  ⌜fn = "is_odd"⌝ ∗ ∃ (x:Z), ⌜vs = [ #x ] ∧ (0 ≤ x)%Z⌝ ∗
  Φ (# (Z.odd x)).

Definition is_even_proto fn vs Φ : iProp Σ :=
  ⌜fn = "is_even"⌝ ∗ ∃ (x:Z), ⌜vs = [ #x ] ∧ (0 ≤ x)%Z⌝ ∗
  Φ (# (Z.even x)).

Definition even_env : prog_environ C_lang Σ := {|
  penv_prog := {[ "is_even" := is_even_func ]};
  penv_proto := (λ fn vs Φ, is_odd_proto fn vs Φ);
|}.

Definition odd_env : prog_environ C_lang Σ := {|
  penv_prog := {[ "is_odd" := is_odd_func ]};
  penv_proto := (λ fn vs Φ, is_even_proto fn vs Φ);
|}.

Lemma is_even_spec (x:Z) E :
  (0 ≤ x)%Z →
  ⊢ WP subst "x" (#x) (is_even_code "x") @ even_env; E
      {{ λ v, ⌜v = #(Z.even x)⌝ }}.
Proof.
  iIntros (?). iStartProof.
  rewrite /is_even_code /=. cbn; simplify_map_eq.
  Fail wp_pures.
Admitted.

Lemma is_odd_spec (x:Z) E :
  (0 ≤ x)%Z →
  ⊢ WP subst "x" (#x) (is_odd_code "x") @ odd_env; E
      {{ λ v, ⌜v = #(Z.odd x)⌝ }}.
Admitted.

End specs.

From melocoton.interop Require Import linking linking_wp embed_wp.
From melocoton.mlanguage Require Import weakestpre.

Section linking.
Context `{!heapGS_gen hlc Σ}.
Context `{!linkGS Σ}.

Definition penv : prog_environ (link_lang C_mlang C_mlang) Σ := {|
  penv_prog := {[ "is_even" := inl is_even_func; "is_odd" := inr is_odd_func ]};
  penv_proto := (λ _ _ _, False)%I;
|}.

Instance penv_is_link : is_link_environ (penv_to_mlang even_env) (penv_to_mlang odd_env) penv.
Proof.
  constructor.
  { set_solver. }
  { simpl. rewrite !fmap_insert !fmap_empty // -insert_union_l.
    rewrite left_id_L //. }
  { iIntros (? ? ? ? ? ?) "(-> & HT)". simpl in H.
    iDestruct "HT" as (x [-> ?]) "HΦ".
    iExists _. iSplitR.
    { iPureIntro. simpl.
      rewrite (_: func = is_odd_func); [|by simplify_map_eq/=].
      rewrite /is_odd_func /apply_function. reflexivity. }
    iIntros "!> _". iApply wp_wand.
    { iApply wp_embed. by iApply is_odd_spec. }
    iIntros (? ->). iFrame. }
  { iIntros (? ? ? ? ? ?) "(-> & HT)". simpl in H.
    iDestruct "HT" as (x [-> ?]) "HΦ".
    iExists _. iSplitR.
    { iPureIntro. simpl.
      rewrite (_: func = is_even_func); [| by simplify_map_eq/=].
      rewrite /is_even_func /apply_function. reflexivity. }
    iIntros "!> _". iApply wp_wand.
    { iApply wp_embed. by iApply is_even_spec. }
    iIntros (? ->). iFrame. }
  { iIntros (? ? ? ? ?) "(-> & _)". simplify_map_eq/=. }
  { iIntros (? ? ? ? ?) "(-> & _)". simplify_map_eq/=. }
Qed.

End linking.
