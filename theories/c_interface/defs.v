From stdpp Require Export binders strings countable gmap.
From iris.algebra Require Export ofe.
From iris.heap_lang Require Export locations.
From iris.prelude Require Import options.

Declare Scope c_val_scope.
Delimit Scope c_val_scope with CV.

Module C_intf.

(** C values *)

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitLoc (l : loc) | LitFunPtr (x : string).
Inductive val :=
  | LitV (l : base_lit).

Bind Scope c_val_scope with C_intf.val.

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.

Global Instance base_lit_countable : Countable base_lit.
Proof.
 refine (inj_countable' (λ l, match l with
  | LitInt n => (inl (inl n))
  | LitLoc l => (inl (inr l))
  | LitFunPtr p => (inr p)
  end) (λ l, match l with
  | inl (inl n) => LitInt n
  | inl (inr l) => LitLoc l
  | inr p => LitFunPtr p
  end) _); by intros [].
Qed.
Global Instance val_countable : Countable val.
Proof.
  set (enc := fun e => match e with LitV l => l end).
  set (dec := LitV).
  refine (inj_countable' enc dec _).
  by intros [].
Qed.

Global Instance val_inhabited : Inhabited val := populate (LitV (LitInt 0)).
Canonical Structure valO := leibnizO val.

Definition LitBool (b : bool) : base_lit := LitInt (if b then 1%Z else 0%Z).
Definition LitUnit : base_lit := LitInt 0.

(** C state *)

Notation heap_cell := (option (option val)).
Notation Deallocated := (None : heap_cell).
Notation Uninitialized := (Some None : heap_cell).
Notation Storing v := (Some (Some v) : heap_cell).

(** The state: heaps of heap_cells. *)
Notation c_state := (gmap loc (option (option val))).

Global Instance state_inhabited : Inhabited c_state :=
  populate inhabitant.

Canonical Structure stateO := leibnizO c_state.

(* Contiguous regions in the heap, i.e. arrays *)

Definition state_upd_heap (f: gmap loc heap_cell → gmap loc heap_cell) (σ: c_state) : c_state :=
  f σ.
Global Arguments state_upd_heap _ !_ /.

Fixpoint heap_array (l : loc) (vs : list heap_cell) : gmap loc heap_cell :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup l vs ow k :
  heap_array l vs !! k = Some ow ↔
  ∃ j, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ vs !! (Z.to_nat j) = Some ow.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j  & ? & -> & ?)].
    { eexists 0. rewrite loc_add_0. naive_solver lia. }
    eexists (1 + j)%Z. rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & w & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite loc_add_0; eauto. }
    right. split.
    { rewrite -{1}(loc_add_0 l). intros ?%(inj (loc_add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z. rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc heap_cell) (l : loc) (vs : list _) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&w&->&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

End C_intf.

Export C_intf.
