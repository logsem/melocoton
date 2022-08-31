From stdpp Require Import gmap stringmap.
From melocoton.c_toy_lang Require Export lang.
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
  | Var x => bool_decide (x ∈ X)
  | Let x e1 e2 => is_closed_expr (set_binder_insert x X) e2 && is_closed_expr X e1
  | UnOp _ e | Malloc e | Load e =>
     is_closed_expr X e
  | BinOp _ e1 e2 | Free e1 e2 | Store e1 e2 | While e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2  =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | FunCall ef ea => is_closed_expr X ef && forallb (is_closed_expr X) ea
  | Extern _ ea => forallb (is_closed_expr X) ea
  | _ => true
  end.

(* Properties *)
Local Instance set_unfold_elem_of_insert_binder x y X Q :
  SetUnfoldElemOf y X Q →
  SetUnfoldElemOf y (set_binder_insert x X) (Q ∨ BNamed y = x).
Proof. destruct 1; constructor; destruct x; set_solver. Qed.

Lemma is_closed_weaken X Y e : is_closed_expr X e → X ⊆ Y → is_closed_expr Y e.
Proof.
  revert X Y; induction e; try naive_solver (eauto; set_solver).
  + cbn. intros X Y [H1 H2%forallb_True]%andb_True HXY. apply andb_True. split.
    - now apply IHe with X, HXY.
    - apply forallb_True, Forall_forall. intros x Hx. apply H with X. 
      3: assumption. 1: now apply elem_of_list_In. rewrite Forall_forall in H2. now apply H2.
  + cbn. intros X Y H2%forallb_True HXY.
    apply forallb_True, Forall_forall. intros x Hx. apply H with X. 
    3: assumption. 1: now apply elem_of_list_In. rewrite Forall_forall in H2. now apply H2.
Qed.

Lemma is_closed_weaken_empty X e : is_closed_expr ∅ e → is_closed_expr X e.
Proof. intros. by apply is_closed_weaken with ∅, empty_subseteq. Qed.

Lemma is_closed_subst_all X e g :
  is_closed_expr (dom g ∪ X) e →
  is_closed_expr X (subst_all g e).
Proof with eauto using is_closed_weaken with set_solver.
  revert X g.
  induction e=> X g /= ?; destruct_and?; split_and?; simplify_option_eq.
  all: idtac...
  all: repeat match goal with H : ?x ∈ ?l1 ∪ ?l2 |- _ => apply elem_of_union in H; destruct H end.
  - apply elem_of_dom in H. destruct H as [k ->]. easy.
  - destruct (g !! x); naive_solver.
  - destruct x; cbn; split_and?...
    + apply IHe2. cbn in H. eapply is_closed_weaken. 1: apply H.
      rewrite dom_delete. intros x [->%elem_of_singleton|H2]%elem_of_union.
      * set_solver.
      * destruct (decide (s = x)) as [->|Hr].
        -- set_solver.
        -- set_solver.
  - rewrite forallb_True. rewrite forallb_True in H1.
    rewrite Forall_forall. rewrite Forall_forall in H1.
    intros x [xx [<- Hin]]%elem_of_list_In%in_map_iff.
    apply H. 1:easy. apply H1. now apply elem_of_list_In.
  - rewrite forallb_True.
    (* stupid ssreflect *) match goal with HH : Is_true ?H |- _ => rename HH into H1 end.
    rewrite forallb_True in H1.
    rewrite Forall_forall. rewrite Forall_forall in H1.
    intros x [xx [<- Hin]]%elem_of_list_In%in_map_iff.
    apply H. 1:easy. apply H1. now apply elem_of_list_In.
Qed.

Lemma is_closed_subst X e y v :
  is_closed_expr ({[y]} ∪ X) e →
  is_closed_expr X (subst y v e).
Proof.
  intros H. apply is_closed_subst_all. eapply is_closed_weaken. 1:exact H.
  set_solver.
Qed.

Lemma is_closed_subst' X e x v :
  is_closed_expr (set_binder_insert x X) e →
  is_closed_expr X (subst' x v e).
Proof. destruct x; eauto using is_closed_subst. Qed.

Lemma subst_all_is_closed X g e : is_closed_expr X e → dom g ∩ X = ∅ → subst_all g e = e.
Proof.
  revert X g. induction e; intros X g;
   rewrite ?bool_decide_spec; rewrite ?andb_True; cbn; intros;
   repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
  - destruct (g !! x) eqn:Heq. 2:easy.
    apply elem_of_dom_2 in Heq. set_solver.
  - fold is_closed_expr in *. destruct x; f_equal; intuition eauto with set_solver.
    eapply IHe2. 1: exact H1. cbn. set_solver.
  - fold is_closed_expr in *. erewrite map_ext_in. 1: apply map_id.
    intros ea Hin. cbn. eapply H. 1:easy. 2: apply H1.
    rewrite forallb_True in H3. rewrite List.Forall_forall in H3. now apply H3.
  - fold is_closed_expr in *. erewrite map_ext_in. 1: apply map_id.
    intros ea Hin. cbn. eapply H. 1:easy. 2: apply H1.
    rewrite forallb_True in H0. rewrite List.Forall_forall in H0. now apply H0.
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
  - destruct x.
    + cbn. auto using subst_is_closed_empty with f_equal.
    + cbn. rewrite delete_union. auto using subst_is_closed_empty with f_equal.
  - f_equal. 1:easy. erewrite map_map. apply map_ext_in.
    intros a Ha. now apply H.
  - f_equal. erewrite map_map. apply map_ext_in.
    intros a Ha. now apply H.
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

Definition is_closed_function X f := match f with
  Fun lst expr => is_closed_expr (X ∪ list_to_set 
        (flat_map (fun k => match k with BAnon => [] | BNamed l => [l] end) lst)) expr end.

(* The stepping relation preserves closedness *)
Lemma head_step_is_closed (p : gmap string function) e1 σ1 e2 σ2 :
  (forall f e, p !! f = Some e → is_closed_function ∅ e) →
  is_closed_expr ∅ e1 →
  head_step p e1 σ1 e2 σ2 →
  is_closed_expr ∅ e2.
Proof.
  intros Clp Cl1 STEP.
  induction STEP; simpl in *; 
    try apply map_Forall_insert_2; try by naive_solver.
  - subst. repeat apply is_closed_subst'; naive_solver.
  - edestruct (zip_args args va) as [σ'|] eqn:Heq. 2: congruence.
    injection H0. intros <-. clear H0.
    eapply is_closed_subst_all.
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

Lemma subst_all_empty e : subst_all ∅ e = e.
Proof.
  induction e; simplify_map_eq; auto with f_equal.
  + destruct x. 2: rewrite delete_empty. all: simplify_map_eq; rewrite ?Hdel; auto with f_equal.
  + rewrite IHe. f_equal. erewrite map_ext_in. 1: apply map_id. intros a Ha. now apply H.
  + f_equal. erewrite map_ext_in. 1: apply map_id. intros a Ha. now apply H.
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

Fixpoint free_vars (e : expr) : stringset :=
  match e with
  | Var x => {[ x ]}
  | Let (BAnon) e1 e2 => free_vars e2 ∪ free_vars e1
  | Let (BNamed x) e1 e2 => ((free_vars e2) ∖ {[ x ]}) ∪ free_vars e1
  | UnOp _ e | Malloc e | Load e =>
     free_vars e
  | BinOp _ e1 e2 | Free e1 e2 | Store e1 e2 | While e1 e2 =>
     free_vars e1 ∪ free_vars e2
  | If e0 e1 e2  =>
     free_vars e0 ∪ free_vars e1 ∪ free_vars e2
  | FunCall ef ea => free_vars ef ∪ union_list (map free_vars ea)
  | Extern _ ea => union_list (map free_vars ea)
  | _ => ∅
  end.

Lemma free_vars_closed e X : free_vars e ⊆ X → is_closed_expr X e.
Proof.
  induction e in X|-*; intros Hfree; cbn.
  3: destruct x; cbn.
  1-3,5-12: set_solver.
  - cbn in Hfree. apply andb_prop_intro; split. 2: set_solver.
    apply IHe2. apply union_subseteq in Hfree.
    destruct Hfree as [H1 _].
    etransitivity. 2: eapply union_mono. 3: apply H1. 2: reflexivity.
    rewrite union_comm.
    rewrite difference_union.
    set_solver.
  - apply andb_prop_intro. split. 1:set_solver. cbn in Hfree.
    clear IHe. induction ee as [|ea ee IHee]; last (cbn; apply andb_prop_intro; split).
    + easy.
    + apply H. 1: now left. cbn in Hfree.
      set_solver.
    + apply IHee. 2: cbn in Hfree; set_solver.
      intros ei Hin X0. apply H. now right.
  - induction arg as [|ea ee IHee]; last (cbn; apply andb_prop_intro; split).
    + easy.
    + apply H. 1: now left. cbn in Hfree.
      set_solver.
    + apply IHee. 2: cbn in Hfree; set_solver.
      intros ei Hin X0. apply H. now right.
Qed.

Lemma subst_all_free_irrel e g1 g2 : 
  (forall x, x ∈ free_vars e → g1 !! x = g2 !! x)
  → subst_all g1 e = subst_all g2 e.
Proof.
  intros H.
  induction e in H,g1,g2|-*.
  - easy.
  - cbn. rewrite (H x). 2:set_solver. easy.
  - cbn. destruct x.
    + erewrite IHe1, IHe2. 1:reflexivity.
      all: intros x Hx; apply H; cbn; set_solver.
    + erewrite IHe1, IHe2. 1:reflexivity.
      * intros x Hx. destruct (string_eq_dec x s) as [->|Hn].
        -- now rewrite ! lookup_delete.
        -- rewrite ! lookup_delete_ne; try congruence.
           apply H. cbn. set_solver.
      * intros x Hx; apply H; cbn; set_solver.
  - cbn. erewrite IHe; [reflexivity|]. intros ? ?; set_solver.
  - cbn. erewrite IHe1,IHe2; first reflexivity. all: intros ? ?; set_solver.
  - cbn. erewrite IHe; first reflexivity. all: intros ? ?; set_solver.
  - cbn. erewrite IHe1,IHe2; first reflexivity. all: intros ? ?; set_solver.
  - cbn. erewrite IHe; first reflexivity. all: intros ? ?; set_solver.
  - cbn. erewrite IHe1,IHe2; first reflexivity. all: intros ? ?; set_solver.
  - cbn. erewrite IHe1,IHe2,IHe3; first reflexivity. all: intros ? ?; set_solver.
  - cbn. erewrite IHe1,IHe2; first reflexivity. all: intros ? ?; set_solver.
  - cbn. erewrite IHe. 1: erewrite map_ext_in. 1:reflexivity. 2:intros ??; set_solver.
    intros a Ha. apply H0. 1:easy. intros x Hx. apply H. cbn. 
    apply elem_of_union_r, elem_of_union_list. exists (free_vars a); split; last done.
    apply elem_of_list_In, in_map_iff. eexists; done.
  - cbn. erewrite map_ext_in. 1:reflexivity.
    intros a Ha. apply H0. 1:easy. intros x Hx. apply H. cbn. 
    apply elem_of_union_list. exists (free_vars a); split; last done.
    apply elem_of_list_In, in_map_iff. eexists; done.
Qed.

Lemma union_list_map_delete (s : stringset) (x:list stringset) : union_list (map (fun k => k ∖ s) x) = union_list x ∖ s.
Proof.
  apply set_eq.
  intros k. rewrite elem_of_difference !elem_of_union_list. split.
  + intros (X & (x0 & <- & H1)%elem_of_list_In%in_map_iff & (H2 & H3)%elem_of_difference).
    split; last easy. exists x0. split; last done. now apply elem_of_list_In.
  + intros ((X & H2 & H3) & H1). exists (X ∖ s). split; last set_solver.
    apply elem_of_list_In. apply in_map_iff. exists X. split; first done. now apply elem_of_list_In.
Qed.

Lemma subst_free_vars xs e : free_vars (subst_all xs e) = free_vars e ∖ dom xs.
Proof.
  induction e in xs|-*.
  - cbn. set_solver.
  - cbn. destruct lookup eqn:Heq.
    + cbn. apply set_eq. intros k. split; first set_solver.
      intros [->%elem_of_singleton H2]%elem_of_difference.
      exfalso. apply H2, elem_of_dom. eauto.
    + cbn. apply set_eq. intros k. split; last set_solver.
      intros ->%elem_of_singleton. apply elem_of_difference. split; first set_solver.
      intros [? ?]%elem_of_dom. congruence.
  - destruct x.
    + cbn. rewrite IHe1. rewrite IHe2. set_solver.
    + cbn. rewrite IHe1. rewrite IHe2. set_solver.
  - cbn. rewrite IHe. set_solver.
  - cbn. rewrite IHe1 IHe2. set_solver.
  - cbn. rewrite IHe. set_solver.
  - cbn. rewrite IHe1 IHe2. set_solver.
  - cbn. rewrite IHe. set_solver.
  - cbn. rewrite IHe1 IHe2. set_solver.
  - cbn. rewrite IHe1 IHe2 IHe3. set_solver.
  - cbn. rewrite IHe1 IHe2. set_solver.
  - cbn. rewrite IHe. rewrite map_map. erewrite map_ext_in. 2: intros a Ha; by apply H.
    rewrite difference_union_distr_l_L. f_equal.
    rewrite <- union_list_map_delete. now rewrite map_map.
  - cbn. rewrite map_map. erewrite map_ext_in. 2: intros a Ha; by apply H.
    rewrite <- union_list_map_delete. now rewrite map_map.
Qed.