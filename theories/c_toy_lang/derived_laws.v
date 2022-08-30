(** This file extends the HeapLang program logic with some derived laws (not
using the lifting lemmas) about arrays and prophecies.

For utility functions on arrays (e.g., freeing/copying an array), see
[heap_lang.lib.array].  *)

From stdpp Require Import fin_maps.
From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Export primitive_laws.
From melocoton.c_toy_lang Require Import tactics notation.
From iris.prelude Require Import options.

(** The [array] connective is a version of [mapsto] that works
with lists of values. *)

Definition array `{!heapGS Σ} (l : loc) (dq : dfrac) (vs : list (option val)) : iProp Σ :=
  [∗ list] i ↦ v ∈ vs, (l +ₗ i) I↦{dq} v.

(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "l ↦∗{ dq } vs" := (array l dq vs)
  (at level 20, format "l  ↦∗{ dq }  vs") : bi_scope.
Notation "l ↦∗□ vs" := (array l DfracDiscarded vs)
  (at level 20, format "l  ↦∗□  vs") : bi_scope.
Notation "l ↦∗{# q } vs" := (array l (DfracOwn q) vs)
  (at level 20, format "l  ↦∗{# q }  vs") : bi_scope.
Notation "l ↦∗ vs" := (array l (DfracOwn 1) vs)
  (at level 20, format "l  ↦∗  vs") : bi_scope.

(** We have [FromSep] and [IntoSep] instances to split the fraction (via the
[AsFractional] instance below), but not for splitting the list, as that would
lead to overlapping instances. *)

Section lifting.
Context `{!heapGS Σ}.
Context {p:program}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : option val.
Implicit Types vs : list (option val).
Implicit Types l : loc.
Implicit Types sz off : nat.

Global Instance array_timeless l q vs : Timeless (array l q vs) := _.

Global Instance array_fractional l vs : Fractional (λ q, l ↦∗{#q} vs)%I := _.
Global Instance array_as_fractional l q vs :
  AsFractional (l ↦∗{#q} vs) (λ q, l ↦∗{#q} vs)%I q.
Proof. split; done || apply _. Qed.

Lemma array_nil l dq : l ↦∗{dq} [] ⊣⊢ emp.
Proof. by rewrite /array. Qed.

Lemma array_singleton l dq v : l ↦∗{dq} [v] ⊣⊢ l I↦{dq} v.
Proof. by rewrite /array /= right_id loc_add_0. Qed.

Lemma array_app l dq vs ws :
  l ↦∗{dq} (vs ++ ws) ⊣⊢ l ↦∗{dq} vs ∗ (l +ₗ length vs) ↦∗{dq} ws.
Proof.
  rewrite /array big_sepL_app.
  setoid_rewrite Nat2Z.inj_add.
  by setoid_rewrite loc_add_assoc.
Qed.

Lemma array_cons l dq v vs : l ↦∗{dq} (v :: vs) ⊣⊢ l I↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs.
Proof.
  rewrite /array big_sepL_cons loc_add_0.
  setoid_rewrite loc_add_assoc.
  setoid_rewrite Nat2Z.inj_succ.
  by setoid_rewrite Z.add_1_l.
Qed.

Global Instance array_cons_frame l dq v vs R Q :
  Frame false R (l I↦{dq} v ∗ (l +ₗ 1) ↦∗{dq} vs) Q →
  Frame false R (l ↦∗{dq} (v :: vs)) Q | 2.
Proof. by rewrite /Frame array_cons. Qed.

Lemma update_array l dq vs off v :
  vs !! off = Some v →
  ⊢ l ↦∗{dq} vs -∗ ((l +ₗ off) I↦{dq} v ∗ ∀ v', (l +ₗ off) I↦{dq} v' -∗ l ↦∗{dq} <[off:=v']>vs).
Proof.
  iIntros (Hlookup) "Hl".
  rewrite -[X in (l ↦∗{_} X)%I](take_drop_middle _ off v); last done.
  iDestruct (array_app with "Hl") as "[Hl1 Hl]".
  iDestruct (array_cons with "Hl") as "[Hl2 Hl3]".
  assert (off < length vs) as H by (apply lookup_lt_is_Some; by eexists).
  rewrite take_length min_l; last by lia. iFrame "Hl2".
  iIntros (w) "Hl2".
  clear Hlookup. assert (<[off:=w]> vs !! off = Some w) as Hlookup.
  { apply list_lookup_insert. lia. }
  rewrite -[in (l ↦∗{_} <[off:=w]> vs)%I](take_drop_middle (<[off:=w]> vs) off w Hlookup).
  iApply array_app. rewrite take_insert; last by lia. iFrame.
  iApply array_cons. rewrite take_length min_l; last by lia. iFrame.
  rewrite drop_insert_gt; last by lia. done.
Qed.

(** * Rules for allocation *)
Lemma mapsto_seq_array l dq v n :
  ([∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) I↦{dq} v) -∗
  l ↦∗{dq} replicate n v.
Proof.
  rewrite /array. iInduction n as [|n'] "IH" forall (l); simpl.
  { done. }
  iIntros "[$ Hl]". rewrite -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc. iApply "IH". done.
Qed.

Lemma twp_Malloc s E n :
  (0 < n)%Z →
  [[{ True }]] Malloc (Val $ LitV $ LitInt $ n) @ s; E
  [[{ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) None ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply twp_Malloc_seq; [done..|].
  iIntros (l) "Hlm". iApply "HΦ".
  iDestruct (big_sepL_sep with "Hlm") as "[Hl $]".
  by iApply mapsto_seq_array.
Qed.
Lemma wp_Malloc s E n :
  (0 < n)%Z →
  {{{ True }}} Malloc (Val $ LitV $ LitInt $ n) @ s; E
  {{{ l, RET LitV (LitLoc l); l ↦∗ replicate (Z.to_nat n) None ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (? Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_Malloc; [auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_Malloc_vec s E n :
  (0 < n)%Z →
  [[{ True }]]
    Malloc #n @ s ; E
  [[{ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) None ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply twp_Malloc; [ lia | done | .. ].
  iIntros (l) "[Hl Hm]". iApply "HΦ". rewrite vec_to_list_replicate. iFrame.
Qed.
Lemma wp_Malloc_vec s E n :
  (0 < n)%Z →
  {{{ True }}}
    Malloc #n @ s ; E
  {{{ l, RET #l; l ↦∗ vreplicate (Z.to_nat n) None ∗
         [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (? Φ) "_ HΦ". iApply (twp_wp_step with "HΦ").
  iApply twp_Malloc_vec; [auto..|]; iIntros (l) "H HΦ". by iApply "HΦ".
Qed.

(** * Rules for accessing array elements *)
Lemma twp_load_offset s E l dq off vs (v:val) :
  vs !! off = Some (Some v) →
  [[{ l ↦∗{dq} vs }]] * #(l +ₗ off) @ s; E [[{ RET v; l ↦∗{dq} vs }]].
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_load with "Hl1"). iIntros "Hl1". iApply "HΦ".
  iDestruct ("Hl2" $! (Some v)) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_load_offset s E l dq off vs (v:val) :
  vs !! off = Some (Some v) →
  {{{ ▷ l ↦∗{dq} vs }}} * #(l +ₗ off) @ s; E {{{ RET v; l ↦∗{dq} vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_load_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

(*
Lemma twp_load_offset_vec s E l dq sz (off : fin sz) (vs : vec (option val) sz) :
  [[{ l ↦∗{dq} vs }]] * #(l +ₗ off) @ s; E [[{ RET vs !!! off; l ↦∗{dq} vs }]].
Proof. apply twp_load_offset. by apply vlookup_lookup. Qed.
Lemma wp_load_offset_vec s E l dq sz (off : fin sz) (vs : vec val sz) :
  {{{ ▷ l ↦∗{dq} vs }}} ! #(l +ₗ off) @ s; E {{{ RET vs !!! off; l ↦∗{dq} vs }}}.
Proof. apply wp_load_offset. by apply vlookup_lookup. Qed. *)

Lemma twp_store_offset s E l off vs (v:val) :
  is_Some (vs !! off) →
  [[{ l ↦∗ vs }]] #(l +ₗ off) <- v @ s; E [[{ RET #0; l ↦∗ <[off:=Some v]> vs }]].
Proof.
  iIntros ([w Hlookup] Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_store with "Hl1"). iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_store_offset s E l off vs (v:val) :
  is_Some (vs !! off) →
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #0; l ↦∗ <[off:=Some v]> vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_store_offset_vec s E l sz (off : fin sz) (vs : vec (option val) sz) (v:val) :
  [[{ l ↦∗ vs }]] #(l +ₗ off) <- v @ s; E [[{ RET #0; l ↦∗ vinsert off (Some v) vs }]].
Proof.
  setoid_rewrite vec_to_list_insert. apply twp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.
Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec (option val) sz) (v:val) :
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #0; l ↦∗ vinsert off (Some v) vs }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_store_offset_vec with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.
(*
Lemma twp_xchg_offset s E l off vs v v' :
  vs !! off = Some v →
  [[{ l ↦∗ vs }]] Xchg #(l +ₗ off) v' @ s; E [[{ RET v; l ↦∗ <[off:=v']> vs }]].
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_xchg with "Hl1"). iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_xchg_offset s E l off vs v v' :
  vs !! off = Some v →
  {{{ ▷ l ↦∗ vs }}} Xchg #(l +ₗ off) v' @ s; E {{{ RET v; l ↦∗ <[off:=v']> vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_xchg_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_xchg_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  [[{ l ↦∗ vs }]] Xchg #(l +ₗ off) v @ s; E [[{ RET (vs !!! off); l ↦∗ vinsert off v vs }]].
Proof.
  setoid_rewrite vec_to_list_insert. apply twp_xchg_offset.
  by apply vlookup_lookup.
Qed.
Lemma wp_xchg_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
   {{{ ▷ l ↦∗ vs }}} Xchg #(l +ₗ off) v @ s; E {{{ RET (vs !!! off); l ↦∗ vinsert off v vs }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_xchg_offset_vec with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_suc_offset s E l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  [[{ l ↦∗ vs }]]
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  [[{ RET (v', #true); l ↦∗ <[off:=v2]> vs }]].
Proof.
  iIntros (Hlookup ?? Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_cmpxchg_suc with "Hl1"); [done..|].
  iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_cmpxchg_suc_offset s E l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (v', #true); l ↦∗ <[off:=v2]> vs }}}.
Proof.
  iIntros (??? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_suc_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  [[{ l ↦∗ vs }]]
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  [[{ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs }]].
Proof.
  intros. setoid_rewrite vec_to_list_insert.
  apply twp_cmpxchg_suc_offset; [|done..].
  by apply vlookup_lookup.
Qed.
Lemma wp_cmpxchg_suc_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs }}}.
Proof.
  iIntros (?? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_suc_offset_vec with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_fail_offset s E l dq off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  [[{ l ↦∗{dq} vs }]]
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  [[{ RET (v0, #false); l ↦∗{dq} vs }]].
Proof.
  iIntros (Hlookup HNEq Hcmp Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_cmpxchg_fail with "Hl1"); first done.
  { destruct Hcmp; by [ left | right ]. }
  iIntros "Hl1". iApply "HΦ". iDestruct ("Hl2" $! v0) as "Hl2".
  rewrite list_insert_id; last done. iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_cmpxchg_fail_offset s E l dq off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  {{{ ▷ l ↦∗{dq} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (v0, #false); l ↦∗{dq} vs }}}.
Proof.
  iIntros (??? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_cmpxchg_fail_offset with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

Lemma twp_cmpxchg_fail_offset_vec s E l dq sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  [[{ l ↦∗{dq} vs }]]
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  [[{ RET (vs !!! off, #false); l ↦∗{dq} vs }]].
Proof.
  intros. apply twp_cmpxchg_fail_offset; [|done..].
  by apply vlookup_lookup.
Qed.
Lemma wp_cmpxchg_fail_offset_vec s E l dq sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗{dq} vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (vs !!! off, #false); l ↦∗{dq} vs }}}.
Proof.
  intros. eapply wp_cmpxchg_fail_offset; [|done..].
  by apply vlookup_lookup.
Qed.

Lemma twp_faa_offset s E l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  [[{ l ↦∗ vs }]] FAA #(l +ₗ off) #i2 @ s; E
  [[{ RET LitV (LitInt i1); l ↦∗ <[off:=#(i1 + i2)]> vs }]].
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (twp_faa with "Hl1").
  iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.
Lemma wp_faa_offset s E l off vs (i1 i2 : Z) :
  vs !! off = Some #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ <[off:=#(i1 + i2)]> vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa_offset with "H"); [by eauto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

Lemma twp_faa_offset_vec s E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  [[{ l ↦∗ vs }]] FAA #(l +ₗ off) #i2 @ s; E
  [[{ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs }]].
Proof.
  intros. setoid_rewrite vec_to_list_insert. apply twp_faa_offset.
  by apply vlookup_lookup.
Qed.
Lemma wp_faa_offset_vec s E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs }}}.
Proof.
  iIntros (? Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_faa_offset_vec with "H"); [by eauto..|]; iIntros "H HΦ".
  by iApply "HΦ".
Qed.

(** Derived prophecy laws *)

(** Lemmas for some particular expression inside the [Resolve]. *)
Lemma wp_resolve_proph s E (p : proph_id) (pvs : list (val * val)) v :
  {{{ proph p pvs }}}
    ResolveProph (Val $ LitV $ LitProphecy p) (Val v) @ s; E
  {{{ pvs', RET (LitV LitUnit); ⌜pvs = (LitV LitUnit, v)::pvs'⌝ ∗ proph p pvs' }}}.
Proof.
  iIntros (Φ) "Hp HΦ". iApply (wp_resolve with "Hp"); first done.
  iApply lifting.wp_pure_step_later; first done. iApply wp_value.
  iIntros "!>" (vs') "HEq Hp". iApply "HΦ". iFrame.
Qed.

Lemma wp_resolve_cmpxchg_suc s E l (p : proph_id) (pvs : list (val * val)) v1 v2 v :
  vals_compare_safe v1 v1 →
  {{{ proph p pvs ∗ ▷ l ↦ v1 }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v1, #true) ; ∃ pvs', ⌜pvs = ((v1, #true)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦ v2 }}}.
Proof.
  iIntros (Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  assert (val_is_unboxed v1) as Hv1; first by destruct Hcmp.
  iApply (wp_cmpxchg_suc with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.

Lemma wp_resolve_cmpxchg_fail s E l (p : proph_id) (pvs : list (val * val)) dq v' v1 v2 v :
  v' ≠ v1 → vals_compare_safe v' v1 →
  {{{ proph p pvs ∗ ▷ l ↦{dq} v' }}}
    Resolve (CmpXchg #l v1 v2) #p v @ s; E
  {{{ RET (v', #false) ; ∃ pvs', ⌜pvs = ((v', #false)%V, v)::pvs'⌝ ∗ proph p pvs' ∗ l ↦{dq} v' }}}.
Proof.
  iIntros (NEq Hcmp Φ) "[Hp Hl] HΦ".
  iApply (wp_resolve with "Hp"); first done.
  iApply (wp_cmpxchg_fail with "Hl"); [done..|]. iIntros "!> Hl".
  iIntros (pvs' ->) "Hp". iApply "HΦ". eauto with iFrame.
Qed.
*)
End lifting.

#[export] Typeclasses Opaque array.
