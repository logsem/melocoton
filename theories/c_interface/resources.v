From iris.bi Require Import lib.fractional.
From transfinite.base_logic.lib Require Export gen_heap gen_inv_heap fancy_updates.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Import defs.
From iris.prelude Require Import options.

(** Separation logic resources for the C heap *)

Class heapGpre_C {SI:indexT} Σ := HeapGpre {
  heapGpre_gen_heapGpre :> gen_heapPreG loc heap_cell Σ;
  heapGpre_inv_heapGpre :> inv_heapGpreS loc heap_cell Σ;
}.

Class heapG_C {SI:indexT} Σ := HeapG {
  heapG_gen_heapG :> gen_heapG loc heap_cell Σ;
  heapG_inv_heapG :> inv_heapG loc heap_cell Σ;
}.

Definition public_state_interp `{SI: indexT} {Σ: gFunctors} `{!heapG_C Σ} :
   c_state → iProp Σ := gen_heap_interp.

(** Since we use an [option val] instance of [gen_heap], we need to overwrite
the notations.  That also helps for scopes and coercions. *)
(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)

Notation "l O↦C{ dq } v" := (mapsto (L:=loc) (V:=heap_cell) l dq (v))
  (at level 20, format "l  O↦C{ dq }  v") : bi_scope.
Notation "l O↦C□ v" := (mapsto (L:=loc) (V:=heap_cell) l DfracDiscarded (v))
  (at level 20, format "l  O↦C□  v") : bi_scope.
Notation "l O↦C{# q } v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn q) (v))
  (at level 20, format "l  O↦C{# q }  v") : bi_scope.
Notation "l O↦C v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn 1) (v))
  (at level 20, format "l  O↦C  v") : bi_scope.

Notation "l I↦C{ dq } v" := (mapsto (L:=loc) (V:=heap_cell) l dq (Some v))
  (at level 20, format "l  I↦C{ dq }  v") : bi_scope.
Notation "l I↦C□ v" := (mapsto (L:=loc) (V:=heap_cell) l DfracDiscarded (Some v))
  (at level 20, format "l  I↦C□  v") : bi_scope.
Notation "l I↦C{# q } v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn q) (Some v))
  (at level 20, format "l  I↦C{# q }  v") : bi_scope.
Notation "l I↦C v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn 1) (Some v))
  (at level 20, format "l  I↦C  v") : bi_scope.

Notation "l ↦C{ dq } v" := (mapsto (L:=loc) (V:=heap_cell) l dq (Some (Some v%CV)))
  (at level 20, format "l  ↦C{ dq }  v") : bi_scope.
Notation "l ↦C□ v" := (mapsto (L:=loc) (V:=heap_cell) l DfracDiscarded (Storing v%CV))
  (at level 20, format "l  ↦C□  v") : bi_scope.
Notation "l ↦C{# q } v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn q) (Storing v%CV))
  (at level 20, format "l  ↦C{# q }  v") : bi_scope.
Notation "l ↦C v" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn 1) (Storing v%CV))
  (at level 20, format "l  ↦C  v") : bi_scope.
Notation "l ↦C{ dq } '?'" := (mapsto (L:=loc) (V:=heap_cell) l dq (Uninitialized))
  (at level 20, format "l  ↦C{ dq }  ?") : bi_scope.
Notation "l ↦C□ '?'" := (mapsto (L:=loc) (V:=heap_cell) l DfracDiscarded (Uninitialized))
  (at level 20, format "l  ↦C□  ?") : bi_scope.
Notation "l ↦C{# q } '?'" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn q) (Uninitialized))
  (at level 20, format "l  ↦C{# q }  ?") : bi_scope.
Notation "l ↦C '?'" := (mapsto (L:=loc) (V:=heap_cell) l (DfracOwn 1) (Uninitialized))
  (at level 20, format "l  ↦C  ?") : bi_scope.

(** Same for [gen_inv_heap], except that these are higher-order notations so to
make setoid rewriting in the predicate [I] work we need actual definitions
here. *)
Section definitions.
  Context {SI:indexT}.
  Context `{!heapG_C Σ}.

  Definition from_storing (I : val → Prop) (Puninit Pfree : Prop) (k : heap_cell) :=
    match k with
    | None => Pfree
    | Some None => Puninit
    | Some (Some v) => I v
    end.

  Definition inv_mapsto_own (l : loc) (v : val) (I : val → Prop) : iProp Σ :=
    inv_mapsto_own l (Storing v) (from_storing I False False).
  Definition inv_mapsto (l : loc) (I : val → Prop) : iProp Σ :=
    inv_mapsto l (from_storing I False False).
End definitions.

Global Instance: Params (@inv_mapsto_own) 4 := {}.
Global Instance: Params (@inv_mapsto) 3 := {}.

Notation inv_heap_inv := (inv_heap_inv loc heap_cell).
Notation "l '↦C_' I □" := (inv_mapsto l I%stdpp%type)
  (at level 20, I at level 9, format "l  '↦C_' I  '□'") : bi_scope.
Notation "l ↦C_ I v" := (inv_mapsto_own l v I%stdpp%type)
  (at level 20, I at level 9, format "l  ↦C_ I  v") : bi_scope.


(** The [array] connective is a version of [mapsto] that works
    with lists of values. *)

Definition array {SI:indexT} `{!heapG_C Σ} (l : loc) (dq : dfrac) (vs : list (option val)) : iProp Σ :=
  [∗ list] i ↦ v ∈ vs, (l +ₗ i) I↦C{dq} v.

(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "l ↦C∗{ dq } vs" := (array l dq vs)
  (at level 20, format "l  ↦C∗{ dq }  vs") : bi_scope.
Notation "l ↦C∗□ vs" := (array l DfracDiscarded vs)
  (at level 20, format "l  ↦C∗□  vs") : bi_scope.
Notation "l ↦C∗{# q } vs" := (array l (DfracOwn q) vs)
  (at level 20, format "l  ↦C∗{# q }  vs") : bi_scope.
Notation "l ↦C∗ vs" := (array l (DfracOwn 1) vs)
  (at level 20, format "l  ↦C∗  vs") : bi_scope.


(** Points-to laws *)

Section Laws.
Context {SI:indexT}.
Context `{!heapG_C Σ, !invG Σ}.

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val]. *)

Lemma mapsto_valid l dq v : l ↦C{dq} v -∗ ⌜✓ dq⌝.
Proof. apply mapsto_valid. Qed.
Lemma mapsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦C{dq1} v1 -∗ l ↦C{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  iIntros "H1 H2". iDestruct (mapsto_valid_2 with "H1 H2") as %[? [=?]]. done.
Qed.
Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦C{dq1} v1 -∗ l ↦C{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %[=?]. done. Qed.

Lemma mapsto_combine l dq1 dq2 v1 v2 :
  l ↦C{dq1} v1 -∗ l ↦C{dq2} v2 -∗ l ↦C{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hl1 Hl2". iDestruct (mapsto_combine with "Hl1 Hl2") as "[$ Heq]".
  by iDestruct "Heq" as %[= ->].
Qed.

Lemma mapsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦C{dq1} v1 -∗ l2 ↦C{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_frac_ne. Qed.
Lemma mapsto_ne l1 l2 dq2 v1 v2 : l1 ↦C v1 -∗ l2 ↦C{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_ne. Qed.

Lemma mapsto_persist l dq v : l ↦C{dq} v ==∗ l ↦C□ v.
Proof. apply mapsto_persist. Qed.

Global Instance inv_mapsto_own_proper l v :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_mapsto_own l v).
Proof.
  intros I1 I2 HI. rewrite /inv_mapsto_own. f_equiv=>-[[w|]|]; [|done|done].
  simpl. apply HI.
Qed.
Global Instance inv_mapsto_proper l :
  Proper (pointwise_relation _ iff ==> (≡)) (inv_mapsto l).
Proof.
  intros I1 I2 HI. rewrite /inv_mapsto. f_equiv=>-[[w|]|]; [|done|done].
  simpl. apply HI.
Qed.

Lemma make_inv_mapsto l v (I : val → Prop) E :
  ↑inv_heapN ⊆ E →
  I v →
  inv_heap_inv -∗ l ↦C v ={E}=∗ l ↦C_I v.
Proof. iIntros (??) "#HI Hl". iApply make_inv_mapsto; done. Qed.
Lemma inv_mapsto_own_inv l v I : l ↦C_I v -∗ l ↦C_I □.
Proof. apply inv_mapsto_own_inv. Qed.

Lemma inv_mapsto_own_acc_strong E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv ={E, E ∖ ↑inv_heapN}=∗ ∀ l v I, l ↦C_I v -∗
    (⌜I v⌝ ∗ l ↦C v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦C w ==∗
      inv_mapsto_own l w I ∗ |={E ∖ ↑inv_heapN, E}=> True)).
Proof.
  iIntros (?) "#Hinv".
  iMod (inv_mapsto_own_acc_strong with "Hinv") as "Hacc"; first done.
  iIntros "!>" (l v I) "Hl". iDestruct ("Hacc" with "Hl") as "(% & Hl & Hclose)".
  iFrame "%∗". iIntros (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_mapsto_own_acc E l v I:
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦C_I v ={E, E ∖ ↑inv_heapN}=∗
    (⌜I v⌝ ∗ l ↦C v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦C w ={E ∖ ↑inv_heapN, E}=∗ l ↦C_I w)).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_mapsto_own_acc with "Hinv Hl") as "(% & Hl & Hclose)"; first done.
  iFrame "%∗". iIntros "!>" (w) "% Hl". iApply "Hclose"; done.
Qed.

Lemma inv_mapsto_acc l I E :
  ↑inv_heapN ⊆ E →
  inv_heap_inv -∗ l ↦C_I □ ={E, E ∖ ↑inv_heapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦C v ∗ (l ↦C v ={E ∖ ↑inv_heapN, E}=∗ ⌜True⌝).
Proof.
  iIntros (?) "#Hinv Hl".
  iMod (inv_mapsto_acc with "Hinv Hl") as ([[v|]|]) "(% & Hl & Hclose)"; [done| |done|done].
  iIntros "!>". iExists (v). iFrame "%∗".
Qed.

(* Arrays *)

Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&?)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_mapsto l (v:heap_cell) (n : nat) :
  ([∗ map] l' ↦ ov ∈ heap_array l (replicate n v), gen_heap.mapsto l' (DfracOwn 1) ov) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) O↦C v.
Proof.
  iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Global Instance array_timeless l q vs : Timeless (array l q vs) := _.

Global Instance array_fractional l vs : Fractional (λ q, l ↦C∗{#q} vs)%I := _.
Global Instance array_as_fractional l q vs :
  AsFractional (l ↦C∗{#q} vs) (λ q, l ↦C∗{#q} vs)%I q.
Proof. split; done || apply _. Qed.

Lemma array_nil l dq : l ↦C∗{dq} [] ⊣⊢ emp.
Proof. by rewrite /array. Qed.

Lemma array_singleton l dq v : l ↦C∗{dq} [v] ⊣⊢ l I↦C{dq} v.
Proof. by rewrite /array /= right_id loc_add_0. Qed.

Lemma array_app l dq vs ws :
  l ↦C∗{dq} (vs ++ ws) ⊣⊢ l ↦C∗{dq} vs ∗ (l +ₗ length vs) ↦C∗{dq} ws.
Proof.
  rewrite /array big_sepL_app.
  setoid_rewrite Nat2Z.inj_add.
  by setoid_rewrite loc_add_assoc.
Qed.

Lemma array_cons l dq v vs : l ↦C∗{dq} (v :: vs) ⊣⊢ l I↦C{dq} v ∗ (l +ₗ 1) ↦C∗{dq} vs.
Proof.
  rewrite /array big_sepL_cons loc_add_0.
  setoid_rewrite loc_add_assoc.
  setoid_rewrite Nat2Z.inj_succ.
  by setoid_rewrite Z.add_1_l.
Qed.

Global Instance array_cons_frame l dq v vs R Q :
  Frame false R (l I↦C{dq} v ∗ (l +ₗ 1) ↦C∗{dq} vs) Q →
  Frame false R (l ↦C∗{dq} (v :: vs)) Q | 2.
Proof. by rewrite /Frame array_cons. Qed.

Lemma update_array l dq vs (off : nat) v :
  vs !! off = Some v →
  ⊢ l ↦C∗{dq} vs -∗ ((l +ₗ off) I↦C{dq} v ∗ ∀ v', (l +ₗ off) I↦C{dq} v' -∗ l ↦C∗{dq} <[off:=v']>vs).
Proof.
  iIntros (Hlookup) "Hl".
  rewrite -[X in (l ↦C∗{_} X)%I](take_drop_middle _ off v); last done.
  iDestruct (array_app with "Hl") as "[Hl1 Hl]".
  iDestruct (array_cons with "Hl") as "[Hl2 Hl3]".
  assert (off < length vs) as H by (apply lookup_lt_is_Some; by eexists).
  rewrite take_length min_l; last by lia. iFrame "Hl2".
  iIntros (w) "Hl2".
  clear Hlookup. assert (<[off:=w]> vs !! off = Some w) as Hlookup.
  { apply list_lookup_insert. lia. }
  rewrite -[in (l ↦C∗{_} <[off:=w]> vs)%I](take_drop_middle (<[off:=w]> vs) off w Hlookup).
  iApply array_app. rewrite take_insert; last by lia. iFrame.
  iApply array_cons. rewrite take_length min_l; last by lia. iFrame.
  rewrite drop_insert_gt; last by lia. done.
Qed.

Lemma mapsto_seq_array l dq v n :
  ([∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) I↦C{dq} v) -∗
  l ↦C∗{dq} replicate n v.
Proof.
  rewrite /array. iInduction n as [|n'] "IH" forall (l); simpl.
  { done. }
  iIntros "[$ Hl]". rewrite -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc. iApply "IH". done.
Qed.

End Laws.
