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
Abort.

End specs.
