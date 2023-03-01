From melocoton.ml_toy_lang Require Export lang notation metatheory.
From Autosubst Require Import Autosubst.
From iris.prelude Require Import options.

Inductive type :=
  | TUnit : type
  | TNat : type
  | TBool : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TRec (τ : {bind 1 of type})
  | TVar (x : var)
  | TForall (τ : {bind 1 of type})
  | TExist (τ : {bind 1 of type})
  | Tref (τ : type). (* References are length one. Handling dynamic arrays is difficult *)

Global Instance Ids_type : Ids type. derive. Defined.
Global Instance Rename_type : Rename type. derive. Defined.
Global Instance Subst_type : Subst type. derive. Defined.
Global Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Definition binop_arithmetic (op : bin_op) : bool :=
  match op with
  | PlusOp | MinusOp| MultOp| QuotOp| RemOp| AndOp| OrOp| XorOp| ShiftLOp| ShiftROp => true
  | LeOp| LtOp| EqOp => false
  end.

Definition binop_arithmetic_to_bool (op : bin_op) : bool :=
  match op with
  | PlusOp | MinusOp| MultOp| QuotOp| RemOp| AndOp| OrOp| XorOp| ShiftLOp| ShiftROp | EqOp => false
  | LeOp| LtOp => true
  end.

Definition binop_boolish (op : bin_op) : bool :=
  match op with
  | AndOp| OrOp| XorOp => true
  | _ => false
  end.

Inductive EqType : type → Prop :=
  | EqTUnit : EqType TUnit
  | EqTNat : EqType TNat
  | EqTBool : EqType TBool
  | EQRef τ : EqType (Tref τ).


Inductive program_type := FunType : list type -> type -> program_type.
Definition program_env := gmap string program_type.

Section IndDef.
Context (P : program_env).

Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).
Unset Elimination Schemes.
Inductive typed (Γ : gmap string type) : expr → type → Prop :=
  | Var_typed x τ : Γ !! x = Some τ → Γ ⊢ₜ Var x : τ 
  | Unit_typed : Γ ⊢ₜ  #LitUnit : TUnit
  | Nat_typed (n:Z) : Γ ⊢ₜ # n : TNat
  | Bool_typed (b:bool) : Γ ⊢ₜ # b : TBool
  | BinOp_typed_nat_nat op e1 e2 :
     binop_arithmetic op = true → 
     Γ ⊢ₜ e1 : TNat → Γ ⊢ₜ e2 : TNat → Γ ⊢ₜ BinOp op e1 e2 : TNat
  | BinOp_typed_nat_bool op e1 e2 :
     binop_arithmetic_to_bool op = true → 
     Γ ⊢ₜ e1 : TNat → Γ ⊢ₜ e2 : TNat → Γ ⊢ₜ BinOp op e1 e2 : TBool
  | BinOp_typed_bool op e1 e2 :
     binop_boolish op = true → 
     Γ ⊢ₜ e1 : TBool → Γ ⊢ₜ e2 : TBool → Γ ⊢ₜ BinOp op e1 e2 : TBool
  | BinOp_typed_eq T op e1 e2 :
     EqType T → 
     Γ ⊢ₜ e1 : T → Γ ⊢ₜ e2 : T → Γ ⊢ₜ BinOp op e1 e2 : TBool
  | Pair_typed e1 e2 τ1 τ2 : Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Snd e : τ2
  | InjL_typed e τ1 τ2 : Γ ⊢ₜ e : τ1 → Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 : Γ ⊢ₜ e : τ2 → Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 τ3 :
     Γ ⊢ₜ e0 : TSum τ1 τ2 → Γ ⊢ₜ e1 : (TArrow τ1 τ3) → Γ ⊢ₜ e2 : (TArrow τ2 τ3) →
     Γ ⊢ₜ Case e0 e1 e2 : τ3
  | If_typed e0 e1 e2 τ :
     Γ ⊢ₜ e0 : TBool → Γ ⊢ₜ e1 : τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ If e0 e1 e2 : τ
  | Rec_typed f x e τ1 τ2 :
     (binder_insert f (TArrow τ1 τ2) (binder_insert x τ1 Γ)) ⊢ₜ e : τ2 → Γ ⊢ₜ Rec f x e : TArrow τ1 τ2
  | App_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : TArrow τ1 τ2 → Γ ⊢ₜ e2 : τ1 → Γ ⊢ₜ App e1 e2 : τ2
  | TLam_typed e τ :
     subst (ren (+1)) <$> Γ ⊢ₜ e : τ → Γ ⊢ₜ TLam e : TForall τ
  | TApp_typed e τ τ' : Γ ⊢ₜ e : TForall τ → Γ ⊢ₜ TApp e : τ.[τ'/]
  | Pack_typed e τ τ' :
     Γ ⊢ₜ e : τ.[τ'/] → Γ ⊢ₜ Pack e : TExist τ
  | UnpackIn_typed x e1 e2 τ τ' :
     Γ ⊢ₜ e1 : TExist τ →
     binder_insert x τ (subst (ren (+1)) <$> Γ) ⊢ₜ e2 : τ'.[ren (+1)] →
     Γ ⊢ₜ UnpackIn x e1 e2 : τ'
  | TRoll e τ : Γ ⊢ₜ e : τ.[TRec τ/] → Γ ⊢ₜ Roll e : TRec τ
  | TUnroll e τ : Γ ⊢ₜ e : TRec τ → Γ ⊢ₜ Unroll e : τ.[TRec τ/] 
  | TAlloc e τ : Γ ⊢ₜ e : τ → Γ ⊢ₜ Alloc e (#1) : Tref τ 
  | TLoad e τ : Γ ⊢ₜ e : Tref τ → Γ ⊢ₜ Load e #0 : τ 
  | TStore e e' τ : Γ ⊢ₜ e : Tref τ → Γ ⊢ₜ e' : τ → Γ ⊢ₜ Store e (#0) e' : TUnit 
  | TExtern s el tl tr :
      P !! s = Some (FunType tl tr) →
      Forall2 (typed Γ) el tl →
      Γ ⊢ₜ (Extern s el) : tr (*
  | TCAS e1 e2 e3 τ :
     EqType τ → Γ ⊢ₜ e1 : Tref τ → Γ ⊢ₜ e2 : τ → Γ ⊢ₜ e3 : τ →
     Γ ⊢ₜ CAS e1 e2 e3 : TBool
  | TFAA e1 e2 : Γ ⊢ₜ e1 : Tref TNat → Γ ⊢ₜ e2 : TNat → Γ ⊢ₜ FAA e1 e2 : TNat *)
where "Γ ⊢ₜ e : τ" := (typed Γ e τ).

(* Forall2 (typed Γ) requires special care *)
Lemma typed_ind (P0 : gmap string type → expr → type → Prop) : 
  (∀ (Γ : gmap string type) (x : string) (τ : type), Γ !! x = Some τ → P0 Γ x τ)
→ (∀  Γ : gmap string type, P0 Γ #() TUnit)
→ (∀ (Γ : gmap string type) (n : Z), P0 Γ #n TNat)
→ (∀ (Γ : gmap string type) (b : bool), P0 Γ #b TBool)
→ (∀ (Γ : gmap string type) (op : bin_op) (e1 e2 : expr), binop_arithmetic op = true → Γ ⊢ₜ e1 : TNat → P0 Γ e1 TNat → Γ ⊢ₜ e2 : TNat → P0 Γ e2 TNat → P0 Γ (BinOp op e1 e2) TNat)
→ (∀ (Γ : gmap string type) (op : bin_op) (e1 e2 : expr), binop_arithmetic_to_bool op = true → Γ ⊢ₜ e1 : TNat → P0 Γ e1 TNat → Γ ⊢ₜ e2 : TNat → P0 Γ e2 TNat → P0 Γ (BinOp op e1 e2) TBool)
→ (∀ (Γ : gmap string type) (op : bin_op) (e1 e2 : expr), binop_boolish op = true → Γ ⊢ₜ e1 : TBool → P0 Γ e1 TBool → Γ ⊢ₜ e2 : TBool → P0 Γ e2 TBool → P0 Γ (BinOp op e1 e2) TBool)
→ (∀ (Γ : gmap string type) (T : type) (op : bin_op) (e1 e2 : expr), EqType T → Γ ⊢ₜ e1 : T → P0 Γ e1 T → Γ ⊢ₜ e2 : T → P0 Γ e2 T → P0 Γ (BinOp op e1 e2) TBool)
→ (∀ (Γ : gmap string type) (e1 e2 : expr) (τ1 τ2 : type), Γ ⊢ₜ e1 : τ1 → P0 Γ e1 τ1 → Γ ⊢ₜ e2 : τ2 → P0 Γ e2 τ2 → P0 Γ (e1, e2)%E (TProd τ1 τ2))
→ (∀ (Γ : gmap string type) (e : expr) (τ1 τ2 : type), Γ ⊢ₜ e : TProd τ1 τ2 → P0 Γ e (TProd τ1 τ2) → P0 Γ (Fst e) τ1)
→ (∀ (Γ : gmap string type) (e : expr) (τ1 τ2 : type), Γ ⊢ₜ e : TProd τ1 τ2 → P0 Γ e (TProd τ1 τ2) → P0 Γ (Snd e) τ2)
→ (∀ (Γ : gmap string type) (e : expr) (τ1 τ2 : type), Γ ⊢ₜ e : τ1 → P0 Γ e τ1 → P0 Γ (InjL e) (TSum τ1 τ2))
→ (∀ (Γ : gmap string type) (e : expr) (τ1 τ2 : type), Γ ⊢ₜ e : τ2 → P0 Γ e τ2 → P0 Γ (InjR e) (TSum τ1 τ2))
→ (∀ (Γ : gmap string type) (e0 e1 e2 : expr) (τ1 τ2 τ3 : type), Γ ⊢ₜ e0 : TSum τ1 τ2 → P0 Γ e0 (TSum τ1 τ2) → Γ ⊢ₜ e1 : TArrow τ1 τ3 → P0 Γ e1 (TArrow τ1 τ3) → Γ ⊢ₜ e2 : TArrow τ2 τ3 → P0 Γ e2 (TArrow τ2 τ3) → P0 Γ (Case e0 e1 e2) τ3)
→ (∀ (Γ : gmap string type) (e0 e1 e2 : expr) (τ : type), Γ ⊢ₜ e0 : TBool → P0 Γ e0 TBool → Γ ⊢ₜ e1 : τ → P0 Γ e1 τ → Γ ⊢ₜ e2 : τ → P0 Γ e2 τ → P0 Γ (if: e0 then e1 else e2)%E τ)
→ (∀ (Γ : gmap string type) (f14 x : binder) (e : expr) (τ1 τ2 : type), binder_insert f14 (TArrow τ1 τ2) (binder_insert x τ1 Γ) ⊢ₜ e : τ2 → P0 (binder_insert f14 (TArrow τ1 τ2) (binder_insert x τ1 Γ)) e τ2 → P0 Γ (rec: f14 x := e)%E (TArrow τ1 τ2))
→ (∀ (Γ : gmap string type) (e1 e2 : expr) (τ1 τ2 : type), Γ ⊢ₜ e1 : TArrow τ1 τ2 → P0 Γ e1 (TArrow τ1 τ2) → Γ ⊢ₜ e2 : τ1 → P0 Γ e2 τ1 → P0 Γ (e1 e2) τ2)
→ (∀ (Γ : gmap string type) (e : expr) (τ : type), subst (ren (+1)) <$> Γ ⊢ₜ e : τ → P0 (subst (ren (+1)) <$> Γ) e τ → P0 Γ (Λ: <>, e)%E (TForall τ))
→ (∀ (Γ : gmap string type) (e : expr) (τ τ' : {bind type}), Γ ⊢ₜ e : TForall τ → P0 Γ e (TForall τ) → P0 Γ (TApp e) τ.[τ'/])
→ (∀ (Γ : gmap string type) (e : expr) (τ τ' : type), Γ ⊢ₜ e : τ.[τ'/] → P0 Γ e τ.[τ'/] → P0 Γ (pack:e)%E (TExist τ))
→ (∀ (Γ : gmap string type) (x : binder) (e1 e2 : expr) (τ : {bind type}) (τ' : type),
       Γ ⊢ₜ e1 : TExist τ → P0 Γ e1 (TExist τ) → binder_insert x τ (subst (ren (+1)) <$> Γ) ⊢ₜ e2 : τ'.[ren (+1)] → P0 (binder_insert x τ (subst (ren (+1)) <$> Γ)) e2 τ'.[ren (+1)] → P0 Γ (unpack: x := e2 in e1)%E τ')
→ (∀ (Γ : gmap string type) (e : expr) (τ : {bind type}), Γ ⊢ₜ e : τ.[TRec τ/] → P0 Γ e τ.[TRec τ/] → P0 Γ (roll:e)%E (TRec τ))
→ (∀ (Γ : gmap string type) (e : expr) (τ : {bind type}), Γ ⊢ₜ e : TRec τ → P0 Γ e (TRec τ) → P0 Γ (unroll:e)%E τ.[TRec τ/])
→ (∀ (Γ : gmap string type) (e : expr) (τ : type), Γ ⊢ₜ e : τ → P0 Γ e τ → P0 Γ ((ref e)%E #1) (Tref τ))
→ (∀ (Γ : gmap string type) (e : expr) (τ : type), Γ ⊢ₜ e : Tref τ → P0 Γ e (Tref τ) → P0 Γ ((! e)%E #0) τ)
→ (∀ (Γ : gmap string type) (e e' : expr) (τ : type), Γ ⊢ₜ e : Tref τ → P0 Γ e (Tref τ) → Γ ⊢ₜ e' : τ → P0 Γ e' τ → P0 Γ ((e <- #0)%E e') TUnit)
→ (∀ (Γ : gmap string type) (s : string) (el : list expr) (tl : list type) (tr : type),
       P !! s = Some (FunType tl tr) → Forall2 (P0 Γ) el tl → P0 Γ (Extern s el) tr) → ∀ (Γ : gmap string type) (e : expr) (t : type), Γ ⊢ₜ e : t → P0 Γ e t.
Proof.
  do 27 intros ?.
  fix IH 4. intros ???; destruct 1; try eauto.
  enough (Forall2 (P0 Γ) el tl) by eauto.
  clear H26.
  revert el tl H27. fix IHf 3.
  intros el tl; destruct 1; econstructor.
  1: by eapply IH.
  by eapply IHf.
Qed.

Definition env_subst := subst_all.

Lemma env_subst_lookup vs x v :
  vs !! x = Some v → env_subst vs (Var x) = of_val v.
Proof.
  intros H. cbn. rewrite H. done.
Qed.

Lemma typed_closed Γ τ e : Γ ⊢ₜ e : τ → is_closed_expr (dom Γ) e.
Proof.
  intros H; induction H using typed_ind; cbn; eauto.
  - by eapply bool_decide_pack, elem_of_dom_2.
  - by rewrite !dom_binder_insert in IHtyped.
  - by erewrite dom_fmap_L in IHtyped.
  - eapply andb_prop_intro; split; eauto.
    eapply bool_decide_pack; set_solver.
  - rewrite !dom_binder_insert !dom_fmap_L in IHtyped2. eauto.
  - eapply andb_prop_intro; split; eauto.
    eapply bool_decide_pack; set_solver.
  - eapply andb_prop_intro; split; eauto.
    eapply bool_decide_pack; set_solver.
  - eauto 10.
  - eapply forallb_True, Forall2_Forall_l. 1:done.
    eapply Forall_true. done.
Qed.
Set Elimination Schemes.
End IndDef.


Notation "P ; Γ ⊢ₜ e : τ" := (typed P Γ e τ) (at level 74, e, τ at next level).
