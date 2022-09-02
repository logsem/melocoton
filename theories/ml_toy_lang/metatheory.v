From stdpp Require Import gmap stringmap.
From melocoton.ml_toy_lang Require Export lang.
From iris.prelude Require Import options.

(* This file contains some metatheory about the heap_lang language,
  which is not needed for verifying programs. *)

(* Adding a binder to a set of identifiers. *)
Local Definition set_binder_insert (x : binder) (X : stringset) : stringset :=
  match x with
  | BAnon => X
  | BNamed f => {[f]} ∪ X
  end.

(* Check if expression [e] is closed w.r.t. the set [X] of variable names,
   and that all the values in [e] are closed *)
Fixpoint is_closed_expr (X : stringset) (e : expr) : bool :=
  match e with
  | Val v => is_closed_val v
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed_expr (set_binder_insert f (set_binder_insert x X)) e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Free e | Load e =>
     is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2  =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | Extern _ ea => forallb (is_closed_expr X) ea
  end
with is_closed_val (v : val) : bool :=
  match v with
  | LitV _ => true
  | RecV f x e => is_closed_expr (set_binder_insert f (set_binder_insert x ∅)) e
  | PairV v1 v2 => is_closed_val v1 && is_closed_val v2
  | InjLV v | InjRV v => is_closed_val v
  end.

Definition is_closed_context (g:gmap string val) := map_Forall (fun a b => is_closed_val b) g.

(* Properties *)
Local Instance set_unfold_elem_of_insert_binder x y X Q :
  SetUnfoldElemOf y X Q →
  SetUnfoldElemOf y (set_binder_insert x X) (Q ∨ BNamed y = x).
Proof. destruct 1; constructor; destruct x; set_solver. Qed.

Lemma is_closed_weaken X Y e : is_closed_expr X e → X ⊆ Y → is_closed_expr Y e.
Proof. revert X Y; induction e; try naive_solver (eauto; set_solver).
       + cbn. intros X Y H2%forallb_True HXY.
         apply forallb_True, Forall_forall. intros x Hx.
         rewrite List.Forall_forall in H. apply H with X. 
         3: assumption. 1: now apply elem_of_list_In. rewrite Forall_forall in H2. now apply H2.
Qed.

Lemma is_closed_subst_all X e g :
  is_closed_context g →
  is_closed_expr (dom g ∪ X) e →
  is_closed_expr X (subst_all g e).
Proof with eauto using is_closed_weaken with set_solver.
  revert X g.
  induction e=> X g  HH /= HHyp; destruct_and?; split_and?; simplify_option_eq.
  all: idtac...
  all: repeat match goal with H : ?x ∈ ?l1 ∪ ?l2 |- _ => apply elem_of_union in H; destruct H end.
  - apply elem_of_dom in H as H2. destruct H2 as [k Hrew]; rewrite Hrew. unfold is_closed_context in HH.
    rewrite map_Forall_lookup in HH. eapply HH. by rewrite <- Hrew.
  - destruct (g !! x) eqn:Heq; try naive_solver.
  - cbn. destruct x,f1; cbn; split_and?...
    + apply IHe. 1: unfold is_closed_context in *; now apply map_Forall_delete.
      cbn in HHyp. eapply is_closed_weaken. 1: apply HHyp.
      rewrite dom_delete. intros x [->%elem_of_singleton|H2]%elem_of_union.
      * set_solver.
      * destruct (decide (s = x)) as [->|Hr].
        -- set_solver.
        -- set_solver.
    + apply IHe. 1: unfold is_closed_context in *; now apply map_Forall_delete.
      cbn in HHyp. eapply is_closed_weaken. 1: apply HHyp.
      rewrite dom_delete. intros x [->%elem_of_singleton|H2]%elem_of_union.
      * set_solver.
      * destruct (decide (s = x)) as [->|Hr].
        -- set_solver.
        -- set_solver.
    + apply IHe. 1: unfold is_closed_context in *; now apply map_Forall_delete, map_Forall_delete.
      cbn in HHyp. eapply is_closed_weaken. 1: apply HHyp.
      rewrite dom_delete. intros x [->%elem_of_singleton|H2]%elem_of_union.
      * set_solver.
      * destruct (decide (s = x)) as [->|Hr].
        -- set_solver.
        -- destruct (decide (s0 = x)) as [->|Hr2].
        --- set_solver.
        --- set_solver.
  - rewrite forallb_True.
    rewrite Forall_forall. rewrite Forall_forall in H.
    rewrite forallb_True in HHyp. rewrite Forall_forall in HHyp.
    intros x [xx [<- Hin]]%elem_of_list_In%in_map_iff.
    apply H. 1: now apply elem_of_list_In. 1:easy. eapply HHyp. now apply elem_of_list_In.
Qed.

Lemma is_closed_subst X e y v :
  is_closed_val v →
  is_closed_expr ({[y]} ∪ X) e →
  is_closed_expr X (subst y v e).
Proof.
  intros Hv H. apply is_closed_subst_all. 2: erewrite dom_singleton_L ; exact H.
  unfold is_closed_context. now apply map_Forall_singleton.
Qed.

Lemma is_closed_subst' X e x v :
  is_closed_val v →
  is_closed_expr (set_binder_insert x X) e →
  is_closed_expr X (subst' x v e).
Proof. destruct x; eauto using is_closed_subst. Qed.


Lemma subst_all_is_closed X g e :
  is_closed_expr X e → dom g ∩ X = ∅ → subst_all g e = e.
Proof.
  revert X g. induction e; intros X g;
   rewrite ?bool_decide_spec; rewrite ?andb_True; cbn; intros;
   repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
  - destruct (g !! x) eqn:Heq. 2:easy.
    apply elem_of_dom_2 in Heq. set_solver.
  - fold is_closed_expr in *. destruct x,f1; f_equal; intuition eauto with set_solver.
    all: cbn; cbn in H; eapply IHe.
    1,3,5: exact H.
    all: set_solver.
  - fold is_closed_expr in *. erewrite map_ext_in. 1: apply map_id.
    intros ea' Hin. cbn. rewrite Forall_forall in H. apply H with X.
    * now apply elem_of_list_In.
    * rewrite forallb_True in H0. rewrite List.Forall_forall in H0. now apply H0.
    * set_solver.
Qed.

Lemma subst_is_closed X e x es : is_closed_expr X e → x ∉ X → subst x es e = e.
Proof.
  intros H1 H2. eapply subst_all_is_closed. 1: exact H1. set_solver.
Qed.

Lemma subst_is_closed_empty e x v : is_closed_expr ∅ e → subst x v e = e.
Proof. intros. apply subst_is_closed with (∅:stringset); set_solver. Qed.


Lemma subst_all_comp e g1 g2 :
  subst_all g1 (subst_all g2 e) = subst_all (g2 ∪ g1) e.
Proof.
  intros. induction e in g1,g2|-*; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using subst_is_closed_empty with f_equal.
  - destruct (g2 !! x) eqn:Heq2; [|cbn;destruct (g1 !! x) eqn:Heq1].
    + cbn. erewrite lookup_union_Some_l. 2: exact Heq2. easy.
    + erewrite lookup_union_r. 2: easy. rewrite Heq1. easy.
    + erewrite lookup_union_r. 2: easy. rewrite Heq1. easy.
  - destruct x, f1.
    + cbn. auto using subst_is_closed_empty with f_equal.
    + cbn. rewrite delete_union. auto using subst_is_closed_empty with f_equal.
    + cbn. rewrite delete_union. auto using subst_is_closed_empty with f_equal.
    + cbn. do 2 rewrite delete_union. auto using subst_is_closed_empty with f_equal.
  - f_equal. erewrite map_map. apply map_ext_in.
    intros a Ha. rewrite Forall_forall in H. apply H. now apply elem_of_list_In.
Qed.

Lemma subst_subst e x v v' :
  subst x v (subst x v' e) = subst x v' e.
Proof.
  unfold subst. rewrite subst_all_comp. f_equal.
  apply map_eq_iff. intros i. destruct ({[x := v']} !! i) eqn:Heq.
  - erewrite lookup_union_Some_l. 2: exact Heq. easy.
  - rewrite lookup_union_r. 2:easy. apply lookup_singleton_None in Heq.
    apply lookup_singleton_None. easy.
Qed.

Lemma subst_subst' e x v v' :
  subst' x v (subst' x v' e) = subst' x v' e.
Proof. destruct x; simpl; auto using subst_subst. Qed.

Lemma subst_subst_ne e x y v v' :
  x ≠ y → subst x v (subst y v' e) = subst y v' (subst x v e).
Proof.
  intros H. unfold subst. rewrite !subst_all_comp.
  f_equal. apply map_eq_iff. intros i. rewrite !lookup_union.
  destruct ({[y := v']} !! i) eqn:Heq1; destruct ({[x := v]} !! i) eqn:Heq2; cbn.
  2-4: easy.
  exfalso. apply lookup_singleton_Some in Heq1. apply lookup_singleton_Some in Heq2.
  destruct Heq1, Heq2. congruence.
Qed.

Lemma subst_subst_ne' e x y v v' :
  x ≠ y → subst' x v (subst' y v' e) = subst' y v' (subst' x v e).
Proof. destruct x, y; simpl; auto using subst_subst_ne with congruence. Qed.


Lemma subst_all_empty e : subst_all ∅ e = e.
Proof.
  induction e; simplify_map_eq; auto with f_equal.
  + destruct x,f1; cbn. 2,3,4: repeat rewrite delete_empty. all: simplify_map_eq; rewrite ?Hdel; auto with f_equal.
  + rewrite Forall_forall in H. f_equal. erewrite map_ext_in. 1: apply map_id. intros a Ha. cbn. now apply H, elem_of_list_In.
Qed.

Lemma subst_rec' f y e x v :
  x = f ∨ x = y ∨ x = BAnon →
  subst' x v (Rec f y e) = Rec f y e.
Proof. intros. destruct x; simplify_option_eq; try naive_solver. cbn. f_equal.
  destruct H as [<-|[<-|H3]]. 
  - cbn. destruct y; cbn. all: rewrite <- subst_all_empty; f_equal.
    1: now rewrite delete_singleton. now  rewrite delete_commute delete_singleton delete_empty.
  - cbn. rewrite delete_singleton. destruct f; cbn; try rewrite delete_empty.
    all: apply subst_all_empty.
  - congruence. 
Qed.
(*
Lemma subst_rec_ne' f y e x v :
  (x ≠ f ∨ f = BAnon) → (x ≠ y ∨ y = BAnon) →
  subst' x v (Rec f y e) = Rec f y (subst' x v e).
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed. *)

Lemma bin_op_eval_closed op v1 v2 v' :
  is_closed_val v1 → is_closed_val v2 → bin_op_eval op v1 v2 = Some v' →
  is_closed_val v'.
Proof.
  rewrite /bin_op_eval /bin_op_eval_bool /bin_op_eval_int /bin_op_eval_loc;
    repeat case_match; by naive_solver.
Qed.

Lemma heap_closed_alloc σ l n w :
  (0 < n)%Z →
  is_closed_val w →
  map_Forall (λ _ v, from_option is_closed_val true v) (heap σ) →
  (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap σ !! (l +ₗ i) = None) →
  map_Forall (λ _ v, from_option is_closed_val true v)
             (heap_array l (replicate (Z.to_nat n) w) ∪ heap σ).
Proof.
  intros Hn Hw Hσ Hl.
  eapply (map_Forall_ind
            (λ k v, ((heap_array l (replicate (Z.to_nat n) w) ∪ heap σ)
                       !! k = Some v))).
  - apply map_Forall_empty.
  - intros m i x Hi Hix Hkwm Hm.
    apply map_Forall_insert_2; auto.
    apply lookup_union_Some in Hix; last first.
    { eapply heap_array_map_disjoint;
        rewrite replicate_length Z2Nat.id; auto with lia. }
    destruct Hix as [(?&?&?&?&?&[-> Hlt%inj_lt]%lookup_replicate_1)%heap_array_lookup|
                     [j Hj]%elem_of_map_to_list%elem_of_list_lookup_1].
    + simplify_eq/=. rewrite !Z2Nat.id in Hlt; eauto with lia.
    + apply map_Forall_to_list in Hσ.
      by eapply Forall_lookup in Hσ; eauto; simpl in *.
  - apply map_Forall_to_list, Forall_forall.
    intros [? ?]; apply elem_of_map_to_list.
Qed.

Definition is_closed_ml_function X f := match f with
  MlFun lst expr => is_closed_expr (X ∪ list_to_set 
        (flat_map (fun k => match k with BAnon => [] | BNamed l => [l] end) lst)) expr end.

Lemma zip_args_closed a b c : zip_args a b = Some c -> Forall is_closed_val b -> is_closed_context c.
Proof.
  induction b in a,c|-*; intros H1 H2.
  - destruct a as [|[|x] ar]; cbn in *; try congruence.
    assert (c = ∅) as -> by congruence. apply map_Forall_empty.
  - destruct a as [|[|x] ar]; cbn in *; try congruence.
    + eapply IHb. 1: apply H1. eapply Forall_inv_tail, H2.
    + destruct (zip_args ar b) eqn:Heq; cbn in H1; try congruence.
      injection H1. intros <-. apply map_Forall_insert_2. 
      1: now apply Forall_inv in H2.
      1: eapply IHb. 1: apply Heq. eapply Forall_inv_tail, H2.
Qed.
      

(* The stepping relation preserves closedness *)
Lemma head_step_is_closed {p:ml_program} e1 σ1 obs e2 σ2 es :
  (forall f e, (p:gmap string ml_function) !! f = Some e → is_closed_ml_function ∅ e) →
  is_closed_expr ∅ e1 →
  map_Forall (λ _ v, from_option is_closed_val true v) σ1.(heap) →
  head_step e1 σ1 obs e2 σ2 es →
  is_closed_expr ∅ e2 ∧ Forall (is_closed_expr ∅) es ∧
  map_Forall (λ _ v, from_option is_closed_val true v) σ2.(heap).
Proof.
  intros Clp Cl1 Clσ1 STEP.
  induction STEP; simpl in *; split_and!;
    try apply map_Forall_insert_2; try by naive_solver.
  - subst. repeat apply is_closed_subst'; naive_solver.
  - unfold un_op_eval in *. repeat case_match; naive_solver.
  - eapply bin_op_eval_closed; eauto; naive_solver.
  - by apply heap_closed_alloc.
  - select (_ !! _ = Some _) ltac:(fun H => by specialize (Clσ1 _ _ H)).
  - edestruct (zip_args args va) as [σ'|] eqn:Heq. 2: congruence.
    injection H0. intros <-. clear H0.
    eapply is_closed_subst_all.
    1: {rewrite forallb_True in Cl1. rewrite Forall_map in Cl1. cbn in Cl1.
        eapply zip_args_closed. 1: apply Heq. apply Cl1. }
    specialize (Clp _ _ H).
    cbn in Clp.
    assert (forall a b, a = b -> is_closed_expr a e -> is_closed_expr b e) as Happ by (now intros ? ? ->).
    eapply Happ, Clp.
    clear Happ H.
    induction args as [|[|a] ar IH] in Heq,va,σ'|-*; cbn; destruct va; cbn in *; try congruence.
    + injection Heq. intros <-. set_solver. 
    + eapply IH. apply Heq.
    + unfold option_map in Heq. specialize (IH va). destruct (zip_args ar va) as [σ''|] eqn:Heq2; last congruence.
      specialize (IH σ'' eq_refl). 
      injection Heq. intros <-. set_solver.
Qed.


Lemma subst_all_insert x v vs e :
  subst_all (<[x:=v]>vs) e = subst x v (subst_all (delete x vs) e).
Proof.
  unfold subst. rewrite subst_all_comp. f_equal. apply map_eq_iff.
  intros i. destruct (decide (x = i)) as [->|?].
  + rewrite lookup_insert. rewrite lookup_union_r.
    * now rewrite lookup_singleton.
    * now rewrite lookup_delete.
  + rewrite lookup_insert_ne. 2:easy.
    rewrite lookup_union.
    rewrite lookup_singleton_ne. 2: easy.
    rewrite union_with_right_id.
    now rewrite lookup_delete_ne.
Qed.

Lemma subst_all_binder_insert b v vs e :
  subst_all (binder_insert b v vs) e =
  subst' b v (subst_all (binder_delete b vs) e).
Proof. destruct b; cbn. 1: easy. now rewrite subst_all_insert. Qed.
Lemma subst_all_binder_insert_empty b v e :
  subst_all (binder_insert b v ∅) e = subst' b v e.
Proof. by rewrite subst_all_binder_insert binder_delete_empty subst_all_empty. Qed.

Lemma subst_all_binder_insert_2 b1 v1 b2 v2 vs e :
  subst_all (binder_insert b1 v1 (binder_insert b2 v2 vs)) e =
  subst' b2 v2 (subst' b1 v1 (subst_all (binder_delete b2 (binder_delete b1 vs)) e)).
Proof.
  destruct b1 as [|s1], b2 as [|s2]=> /=; auto using subst_all_insert.
  rewrite subst_all_insert. destruct (decide (s1 = s2)) as [->|].
  - by rewrite delete_idemp subst_subst delete_insert_delete.
  - by rewrite delete_insert_ne // subst_all_insert subst_subst_ne.
Qed.
Lemma subst_all_binder_insert_2_empty b1 v1 b2 v2 e :
  subst_all (binder_insert b1 v1 (binder_insert b2 v2 ∅)) e =
  subst' b2 v2 (subst' b1 v1 e).
Proof.
  by rewrite subst_all_binder_insert_2 !binder_delete_empty subst_all_empty.
Qed.

Lemma subst_all_is_closed_empty e vs : is_closed_expr ∅ e → subst_all vs e = e.
Proof. intros. apply subst_all_is_closed with (∅ : stringset); set_solver. Qed.
