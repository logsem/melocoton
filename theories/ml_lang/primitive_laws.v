(** This file proves the basic laws of the HeapLang program logic by applying
the Iris lifting lemmas. *)

From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From transfinite.base_logic.lib Require Import mono_nat.
From melocoton.interop.extra_ghost_state Require Export persistent_ghost_map.
From melocoton.language Require Export weakestpre lifting.
From melocoton.ml_lang Require Export lang_instantiation class_instances.
From melocoton.ml_lang Require Import tactics notation.
From iris.prelude Require Import options.
From melocoton Require Import monotone.

Local Program Instance MLHeapPGMData : PGMData := {
  K := loc;
  V := list val;
  Vpers := nat;
  Fpers := length;
  Pmap m := True;
}.
Next Obligation. eauto. Qed.
Next Obligation. done. Qed.

Class heapGpre_ML {SI:indexT} Σ := HeapGpre_ML {
  heapGpre_ghost_map :> pgmG Σ MLHeapPGMData;
}.

Class heapG_ML `{SI: indexT} Σ := HeapG_ML {
  heapG_ghost_map :> pgmG Σ MLHeapPGMData;
  γheapGML : gname
}.

Definition heapΣ_ML {SI: indexT} : gFunctors :=
  #[pgmΣ MLHeapPGMData].

Global Instance subG_heapGpre_ML `{SI: indexT} Σ : subG heapΣ_ML Σ → heapGpre_ML Σ.
Proof. solve_inG. Qed.

Local Notation state := (gmap loc ((list val))).


Global Program Instance heapG_langG_ML `{SI: indexT}`{heapG_ML Σ}
      : langG val ML_lang Σ := {
  state_interp σ := pgm_auth γheapGML 1 σ
}.

Notation "l ↦M{ dq } v" := (pgm_elem (D:=MLHeapPGMData) γheapGML l dq ([v%MLV]))
  (at level 20, format "l  ↦M{ dq }  v") : bi_scope.
Notation "l ↦M□ v" := (pgm_elem (D:=MLHeapPGMData) γheapGML l DfracDiscarded ([v%MLV]))
  (at level 20, format "l  ↦M□  v") : bi_scope.
Notation "l ↦M{# q } v" := (pgm_elem (D:=MLHeapPGMData) γheapGML l (DfracOwn q) ([v%MLV]))
  (at level 20, format "l  ↦M{# q }  v") : bi_scope.
Notation "l ↦M v" := (pgm_elem (D:=MLHeapPGMData) γheapGML l (DfracOwn 1) ([v%MLV]))
  (at level 20, format "l  ↦M  v") : bi_scope.

Notation "l ↦∗{ dq } vs" := (pgm_elem (D:=MLHeapPGMData) γheapGML l dq (vs))
  (at level 20, format "l  ↦∗{ dq }  vs") : bi_scope.
Notation "l ↦∗□ vs" := (pgm_elem (D:=MLHeapPGMData) γheapGML l DfracDiscarded (vs))
  (at level 20, format "l  ↦∗□  vs") : bi_scope.
Notation "l ↦∗{# q } vs" := (pgm_elem (D:=MLHeapPGMData) γheapGML l (DfracOwn q) (vs))
  (at level 20, format "l  ↦∗{# q }  vs") : bi_scope.
Notation "l ↦∗ vs" := (pgm_elem (D:=MLHeapPGMData) γheapGML l (DfracOwn 1) (vs))
  (at level 20, format "l  ↦∗  vs") : bi_scope.
Notation "l ↦Mlen n" := (pgm_pers (D:=MLHeapPGMData) γheapGML l n)
  (at level 20, format "l  ↦Mlen  n") : bi_scope.

Section lifting.
Context `{SI: indexT}.
Context `{!heapG_ML Σ, !invG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types l : loc.
Implicit Types pe : prog_environ ML_lang Σ.

(** Recursive functions: we do not use this lemmas as it is easier to use Löb
induction directly, but this demonstrates that we can state the expected
reasoning principle for recursive functions, without any visible ▷. *)
Lemma wp_rec_löb pe E f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WP (rec: f x := e)%MLV v @ pe; E {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WP (subst' x v (subst' f (rec: f x := e)%MLV e))%MLE @ pe; E {{ Φ }}) -∗
  ∀ v, Ψ v -∗ WP (rec: f x := e)%MLV v @ pe; E {{ Φ }}.
Proof.
  iIntros "#Hrec". iLöb as "IH". iIntros (v) "HΨ".
  iApply lifting.wp_pure_step_later; first eauto.
  iIntros "!>". iApply ("Hrec" with "[] HΨ"). iIntros "!>" (w) "HΨ".
  iApply ("IH" with "HΨ").
Qed.

(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [val]. *)

Lemma mapsto_valid l dq v : l ↦M{dq} v -∗ ⌜✓ dq⌝.
Proof. apply pgm_elem_valid. Qed.
Lemma mapsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦M{dq1} v1 -∗ l ↦M{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  iIntros "H1 H2". iDestruct (pgm_elem_valid_2 with "H1 H2") as %[? [=?]]. done.
Qed.
Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦M{dq1} v1 -∗ l ↦M{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iDestruct (pgm_elem_agree with "H1 H2") as %[=?]. done. Qed.

Lemma mapsto_combine l dq1 dq2 v1 v2 :
  l ↦M{dq1} v1 -∗ l ↦M{dq2} v2 -∗ l ↦M{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hl1 Hl2". iDestruct (pgm_elem_combine with "Hl1 Hl2") as "[$ Heq]".
  by iDestruct "Heq" as %[= ->].
Qed. 

Lemma mapsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦M{dq1} v1 -∗ l2 ↦M{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. eapply @pgm_elem_frac_ne. Qed.
Lemma mapsto_ne l1 l2 dq2 v1 v2 : l1 ↦M v1 -∗ l2 ↦M{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply @pgm_elem_ne. Qed.

Lemma mapsto_persist l dq v : l ↦M{dq} v ==∗ l ↦M□ v.
Proof. apply pgm_elem_persist. Qed.

Lemma wp_allocN pe E v n :
  (0 ≤ n)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt n) (Val v) @ pe; E
  {{{ l, RET LitV (LitLoc l); l ↦∗ (replicate (Z.to_nat n) v)}}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1) "Hσ". iModIntro. iSplit; first (destruct n; eauto with lia head_step).
  iIntros (v2 σ2 Hstep). inv_head_step; last lia. iModIntro.
  iMod (@pgm_insert _ _ MLHeapPGMData _ _ _ l ((replicate (Z.to_nat n) v)) with "Hσ") as "(Hσ & Hl)".
  { by apply not_elem_of_dom. }
  1: done.
  iModIntro. iFrame. iApply "HΦ"; iFrame.
Qed.

Lemma wp_alloc pe E v :
  {{{ True }}} Alloc (Val v) @ pe; E
  {{{ l, RET LitV (LitLoc l); l ↦M v }}}.
Proof.
  iIntros (HΦ) "_ HΦ". by iApply wp_allocN.
Qed.

Lemma wp_allocN_wrong_size pe E v n :
  (n < 0)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt n) (Val v) @ pe; E
  {{{ RET v; False }}}.
Proof.
  iIntros (Hn Φ) "_ HΦ". iLöb as "IH".
  iApply wp_lift_step_fupd; first done.
  iIntros (σ1) "Hσ !>". iSplit.
  { iPureIntro. eapply head_prim_reducible. eexists _, _.
    by eapply AllocNWrongSizeS. }
  iIntros (v2 σ2 Hstep).
  eapply head_reducible_prim_step in Hstep; first (inv_head_step; first lia).
  2: { eexists _, _. by eapply AllocNWrongSizeS. }
  do 4 iModIntro. iFrame. by iApply "IH".
Qed.

Lemma wp_loadN pe E l i dq vs v :
  (0 ≤ i)%Z →
  vs !! Z.to_nat i = Some v →
  {{{ ▷ l ↦∗{dq} vs }}} LoadN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i) @ pe; E
  {{{ RET v; l ↦∗{dq} vs }}}.
Proof.
  iIntros (Hi Hv Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1) "Hσ !>". iDestruct (pgm_lookup with "Hσ Hl") as %?.
  assert (σ1 !! l.[i] = Some v).
  { rewrite store_lookup_eq. case_bool_decide; [|done]. by simplify_map_eq/=. }
  iSplit; first by eauto with head_step.
  iIntros (v2 σ2 Hstep); inv_head_step. iNext. iModIntro. iFrame.
  by iApply "HΦ".
Qed.

Lemma wp_loadN_oob pe E l i dq vs :
  (i < 0 ∨ length vs ≤ i)%Z →
  {{{ ▷ l ↦∗{dq} vs }}} LoadN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i) @ pe; E
  {{{ v, RET v; False }}}.
Proof.
  iIntros (Hi Φ) ">Hl HΦ". iLöb as "IH".
  iApply wp_lift_step_fupd; first done.
  iIntros (σ1) "Hσ !>". iDestruct (pgm_lookup with "Hσ Hl") as %?.
  assert (σ1 !! l.[i] = None).
  { rewrite store_lookup_eq. case_bool_decide; [|done]. simplify_map_eq/=.
    destruct Hi; try lia. apply lookup_ge_None_2; lia. }
  iSplit. { iPureIntro. eapply head_prim_reducible. eexists _, _. by eapply LoadNOobS. }
  iIntros (v2 σ2 Hstep).
  eapply head_reducible_prim_step in Hstep; first inv_head_step.
  2: { eexists _, _; by eapply LoadNOobS. }
  do 4 iModIntro. iFrame. by iApply ("IH" with "[$] [$]").
Qed.

Lemma wp_load pe E l dq v :
  {{{ ▷ l ↦M{dq} v }}} Load (Val $ LitV $ LitLoc l) @ pe; E
  {{{ RET v; l ↦M{dq} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply (wp_loadN with "Hl"); try done.
Qed.

Lemma wp_storeN pe E l i vs w :
  (0 ≤ i < length vs)%Z →
  {{{ ▷ l ↦∗ vs }}} StoreN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i) (Val w) @ pe; E
  {{{ RET LitV LitUnit; l ↦∗ <[ Z.to_nat i := w ]> vs }}}.
Proof.
  iIntros (Hi Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1) "Hσ !>". iDestruct (pgm_lookup with "Hσ Hl") as %?.
  assert (is_Some (σ1 !! l.[i])) as [? ?].
  { rewrite store_lookup_eq. case_bool_decide; [|lia]. simplify_map_eq.
    apply lookup_lt_is_Some. lia. }
  iSplit; first by eauto with head_step.
  iIntros (v2 σ2 Hstep); inv_head_step. iModIntro.
  iMod (pgm_update with "Hσ Hl") as "[Hσ Hl]"; last first.
  - rewrite (store_insert_offset _ _ _ vs); auto; [].
    iModIntro. iFrame "Hσ". iApply "HΦ". iApply "Hl".
  - done.
  - cbn. by rewrite insert_length.
Qed.

Lemma wp_storeN_oob pe E l i vs w :
  (i < 0 ∨ length vs ≤ i)%Z →
  {{{ ▷ l ↦∗ vs }}} StoreN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i) (Val w) @ pe; E
  {{{ v, RET v; False }}}.
Proof.
  iIntros (Hi Φ) ">Hl HΦ". iLöb as "IH".
  iApply wp_lift_step_fupd; first done.
  iIntros (σ1) "Hσ !>". iDestruct (pgm_lookup with "Hσ Hl") as %?.
  assert (σ1 !! l.[i] = None).
  { rewrite store_lookup_eq. case_bool_decide; [|done]. simplify_map_eq/=.
    destruct Hi; try lia. apply lookup_ge_None_2; lia. }
  iSplit. { iPureIntro. eapply head_prim_reducible. eexists _, _. by eapply StoreNOobS. }
  iIntros (v2 σ2 Hstep).
  eapply head_reducible_prim_step in Hstep; first inv_head_step.
  2: { eexists _, _; by eapply StoreNOobS. }
  do 4 iModIntro. iFrame.
  iApply ("IH" with "[$] [$]").
Qed.

Lemma wp_store_nochange dq pe E l i vs w :
  (0 ≤ i < length vs)%Z →
  (vs !! (Z.to_nat i) = Some w) →
  {{{ ▷ l ↦∗{dq} vs }}} StoreN (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i) (Val w) @ pe; E
  {{{ RET LitV LitUnit; l ↦∗{dq} vs }}}.
Proof.
  iIntros (Hi Hlu Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1) "Hσ !>". iDestruct (pgm_lookup with "Hσ Hl") as %?.
  assert (σ1 !! l.[i] = Some w) as Heqvs.
  { rewrite store_lookup_eq. case_bool_decide; [|lia]. simplify_map_eq. done. }
  iSplit; first by eauto with head_step.
  iIntros (v2 σ2 Hstep); inv_head_step. iModIntro.
  rewrite (store_insert_offset _ _ _ vs); auto; [].
  rewrite list_insert_id; last done. rewrite insert_id; last done.
  iModIntro. iFrame "Hσ". iApply "HΦ". iApply "Hl". 
Qed.

Lemma wp_store pe E l v w :
  {{{ ▷ l ↦M v }}} Store (Val $ LitV $ LitLoc l) (Val w) @ pe; E
  {{{ RET LitV LitUnit; l ↦M w }}}.
Proof.
  iIntros (Φ) "Hl HΦ". by iApply (wp_storeN with "Hl").
Qed.

Lemma wp_length pe E l dq vs :
  {{{ ▷ l ↦∗{dq} vs }}} Length (Val $ LitV $ LitLoc l) @ pe; E
  {{{ RET LitV $ LitInt (length vs); l ↦∗{dq} vs }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1) "Hσ !>". iDestruct (pgm_lookup with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iIntros (v2 σ2 Hstep); inv_head_step. do 2 iModIntro.
  iFrame. by iApply "HΦ".
Qed.

Lemma wp_length_only pe E l vlen :
  {{{ ▷ l ↦Mlen vlen }}} Length (Val $ LitV $ LitLoc l) @ pe; E
  {{{ RET LitV $ LitInt (vlen); True }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step; first done.
  iIntros (σ1) "Hσ !>". iDestruct (pgm_lookup_pers with "Hσ Hl") as %(v&Hlen&Helem).
  iSplit; first by eauto with head_step.
  iIntros (v2 σ2 Hstep); inv_head_step. do 2 iModIntro.
  iFrame. by iApply "HΦ".
Qed.

(* TODO: rules to allow splitting the ownership of an array, as apparently is done in
   Cosmo. *)

End lifting.
