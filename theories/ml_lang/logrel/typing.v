From melocoton.ml_lang Require Export lang notation metatheory.
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
  | TArray (τ : type).

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
  | EQTArray τ : EqType (TArray τ).


Inductive program_type := FunType : list type -> type -> program_type.
Definition subst_prog_type (f : var → type) : program_type → program_type := fun '(FunType tv tr) => FunType (fmap (subst f) tv) (subst f tr).
Definition program_env := gmap string program_type.
Definition subst_prog_env f (p : program_env) := fmap (subst_prog_type f) p.

Section IndDef.

Reserved Notation "P ;; Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).
Unset Elimination Schemes.
Inductive typed (P : program_env) (Γ : gmap string type) : expr → type → Prop :=
  | Var_typed x τ : Γ !! x = Some τ → P ;; Γ ⊢ₜ Var x : τ
  | Unit_typed : P ;; Γ ⊢ₜ  #LitUnit : TUnit
  | Nat_typed (n:Z) : P ;; Γ ⊢ₜ # n : TNat
  | Bool_typed (b:bool) : P ;; Γ ⊢ₜ # b : TBool
  | BinOp_typed_nat_nat op e1 e2 :
     binop_arithmetic op = true → 
     P ;; Γ ⊢ₜ e1 : TNat → P ;; Γ ⊢ₜ e2 : TNat → P ;; Γ ⊢ₜ BinOp op e1 e2 : TNat
  | BinOp_typed_nat_bool op e1 e2 :
     binop_arithmetic_to_bool op = true → 
     P ;; Γ ⊢ₜ e1 : TNat → P ;; Γ ⊢ₜ e2 : TNat → P ;; Γ ⊢ₜ BinOp op e1 e2 : TBool
  | BinOp_typed_bool op e1 e2 :
     binop_boolish op = true → 
     P ;; Γ ⊢ₜ e1 : TBool → P ;; Γ ⊢ₜ e2 : TBool → P ;; Γ ⊢ₜ BinOp op e1 e2 : TBool
  | BinOp_typed_eq T e1 e2 :
     EqType T → 
     P ;; Γ ⊢ₜ e1 : T → P ;; Γ ⊢ₜ e2 : T → P ;; Γ ⊢ₜ BinOp EqOp e1 e2 : TBool
  | Pair_typed e1 e2 τ1 τ2 : P ;; Γ ⊢ₜ e1 : τ1 → P ;; Γ ⊢ₜ e2 : τ2 → P ;; Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : P ;; Γ ⊢ₜ e : TProd τ1 τ2 → P ;; Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 : P ;; Γ ⊢ₜ e : TProd τ1 τ2 → P ;; Γ ⊢ₜ Snd e : τ2
  | InjL_typed e τ1 τ2 : P ;; Γ ⊢ₜ e : τ1 → P ;; Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 : P ;; Γ ⊢ₜ e : τ2 → P ;; Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 τ3 :
     P ;; Γ ⊢ₜ e0 : TSum τ1 τ2 → P ;; Γ ⊢ₜ e1 : (TArrow τ1 τ3) → P ;; Γ ⊢ₜ e2 : (TArrow τ2 τ3) →
     P ;; Γ ⊢ₜ Case e0 e1 e2 : τ3
  | If_typed e0 e1 e2 τ :
     P ;; Γ ⊢ₜ e0 : TBool → P ;; Γ ⊢ₜ e1 : τ → P ;; Γ ⊢ₜ e2 : τ → P ;; Γ ⊢ₜ If e0 e1 e2 : τ
  | Rec_typed f x e τ1 τ2 :
     P ;; (binder_insert f (TArrow τ1 τ2) (binder_insert x τ1 Γ)) ⊢ₜ e : τ2 → P ;; Γ ⊢ₜ Rec f x e : TArrow τ1 τ2
  | App_typed e1 e2 τ1 τ2 :
     P ;; Γ ⊢ₜ e1 : TArrow τ1 τ2 → P ;; Γ ⊢ₜ e2 : τ1 → P ;; Γ ⊢ₜ App e1 e2 : τ2
  | TLam_typed e τ :
     subst_prog_env (ren (+1)) P ;; subst (ren (+1)) <$> Γ ⊢ₜ e : τ → P ;; Γ ⊢ₜ TLam e : TForall τ
  | TApp_typed e τ τ' : P ;; Γ ⊢ₜ e : TForall τ → P ;; Γ ⊢ₜ TApp e : τ.[τ'/]
  | Pack_typed e τ τ' :
     P ;; Γ ⊢ₜ e : τ.[τ'/] → P ;; Γ ⊢ₜ Pack e : TExist τ
  | UnpackIn_typed x e1 e2 τ τ' :
     P ;; Γ ⊢ₜ e1 : TExist τ →
     subst_prog_env (ren (+1)) P ;; binder_insert x τ (subst (ren (+1)) <$> Γ) ⊢ₜ e2 : τ'.[ren (+1)] →
     P ;; Γ ⊢ₜ UnpackIn x e1 e2 : τ'
  | TRoll e τ : P ;; Γ ⊢ₜ e : τ.[TRec τ/] → P ;; Γ ⊢ₜ Roll e : TRec τ
  | TUnroll e τ : P ;; Γ ⊢ₜ e : TRec τ → P ;; Γ ⊢ₜ Unroll e : τ.[TRec τ/]
  | TAllocN e1 e2 τ : P ;; Γ ⊢ₜ e1 : TNat → P ;; Γ ⊢ₜ e2 : τ → P ;; Γ ⊢ₜ AllocN e1 e2 : TArray τ
  | TLoadN e1 e2 τ : P ;; Γ ⊢ₜ e1 : TArray τ → P ;; Γ ⊢ₜ e2 : TNat → P ;; Γ ⊢ₜ LoadN e1 e2 : τ
  | TStoreN e1 e2 e3 τ : P ;; Γ ⊢ₜ e1 : TArray τ → P ;; Γ ⊢ₜ e2 : TNat → P ;; Γ ⊢ₜ e3 : τ → P ;; Γ ⊢ₜ StoreN e1 e2 e3 : TUnit
  | TExtern s el tl tr :
      P !! s = Some (FunType tl tr) →
      Forall2 (typed P Γ) el tl →
      P ;; Γ ⊢ₜ (Extern s el) : tr
where "P ;; Γ ⊢ₜ e : τ" := (typed P Γ e τ).

(* Forall2 (typed Γ) requires special care *)
Lemma typed_ind (P : program_env → gmap string type → expr → type → Prop) : 
    (∀ (P0 : program_env) (Γ : gmap string type) (x : string) (τ : type), Γ !! x = Some τ → P P0 Γ x τ)
  → (∀ (P0 : program_env) (Γ : gmap string type), P P0 Γ #() TUnit)
  → (∀ (P0 : program_env) (Γ : gmap string type) (n : Z), P P0 Γ #n TNat)
  → (∀ (P0 : program_env) (Γ : gmap string type) (b : bool), P P0 Γ #b TBool)
  → (∀ (P0 : program_env) (Γ : gmap string type) (op : bin_op) (e1 e2 : expr), binop_arithmetic op = true → P0;; Γ ⊢ₜ e1 : TNat → P P0 Γ e1 TNat → P0;; Γ ⊢ₜ e2 : TNat → P P0 Γ e2 TNat → P P0 Γ (BinOp op e1 e2) TNat)
  → (∀ (P0 : program_env) (Γ : gmap string type) (op : bin_op) (e1 e2 : expr), binop_arithmetic_to_bool op = true → P0;; Γ ⊢ₜ e1 : TNat → P P0 Γ e1 TNat → P0;; Γ ⊢ₜ e2 : TNat → P P0 Γ e2 TNat → P P0 Γ (BinOp op e1 e2) TBool)
  → (∀ (P0 : program_env) (Γ : gmap string type) (op : bin_op) (e1 e2 : expr), binop_boolish op = true → P0;; Γ ⊢ₜ e1 : TBool → P P0 Γ e1 TBool → P0;; Γ ⊢ₜ e2 : TBool → P P0 Γ e2 TBool → P P0 Γ (BinOp op e1 e2) TBool)
  → (∀ (P0 : program_env) (Γ : gmap string type) (T : type) (e1 e2 : expr), EqType T → P0;; Γ ⊢ₜ e1 : T → P P0 Γ e1 T → P0;; Γ ⊢ₜ e2 : T → P P0 Γ e2 T → P P0 Γ (BinOp EqOp e1 e2) TBool)
  → (∀ (P0 : program_env) (Γ : gmap string type) (e1 e2 : expr) (τ1 τ2 : type), P0;; Γ ⊢ₜ e1 : τ1 → P P0 Γ e1 τ1 → P0;; Γ ⊢ₜ e2 : τ2 → P P0 Γ e2 τ2 → P P0 Γ (e1, e2)%MLE (TProd τ1 τ2))
  → (∀ (P0 : program_env) (Γ : gmap string type) (e : expr) (τ1 τ2 : type), P0;; Γ ⊢ₜ e : TProd τ1 τ2 → P P0 Γ e (TProd τ1 τ2) → P P0 Γ (Fst e) τ1)
  → (∀ (P0 : program_env) (Γ : gmap string type) (e : expr) (τ1 τ2 : type), P0;; Γ ⊢ₜ e : TProd τ1 τ2 → P P0 Γ e (TProd τ1 τ2) → P P0 Γ (Snd e) τ2)
  → (∀ (P0 : program_env) (Γ : gmap string type) (e : expr) (τ1 τ2 : type), P0;; Γ ⊢ₜ e : τ1 → P P0 Γ e τ1 → P P0 Γ (InjL e) (TSum τ1 τ2))
  → (∀ (P0 : program_env) (Γ : gmap string type) (e : expr) (τ1 τ2 : type), P0;; Γ ⊢ₜ e : τ2 → P P0 Γ e τ2 → P P0 Γ (InjR e) (TSum τ1 τ2))
  → (∀ (P0 : program_env) (Γ : gmap string type) (e0 e1 e2 : expr) (τ1 τ2 τ3 : type), P0;; Γ ⊢ₜ e0 : TSum τ1 τ2 → P P0 Γ e0 (TSum τ1 τ2) → P0;; Γ ⊢ₜ e1 : TArrow τ1 τ3 → P P0 Γ e1 (TArrow τ1 τ3) → P0;; Γ ⊢ₜ e2 : TArrow τ2 τ3 → P P0 Γ e2 (TArrow τ2 τ3) → P P0 Γ (Case e0 e1 e2) τ3)
  → (∀ (P0 : program_env) (Γ : gmap string type) (e0 e1 e2 : expr) (τ : type), P0;; Γ ⊢ₜ e0 : TBool → P P0 Γ e0 TBool → P0;; Γ ⊢ₜ e1 : τ → P P0 Γ e1 τ → P0;; Γ ⊢ₜ e2 : τ → P P0 Γ e2 τ → P P0 Γ (if: e0 then e1 else e2)%MLE τ)
  → (∀ (P0 : program_env) (Γ : gmap string type) (f14 x : binder) (e : expr) (τ1 τ2 : type), P0;; binder_insert f14 (TArrow τ1 τ2) (binder_insert x τ1 Γ) ⊢ₜ e : τ2 → P P0 (binder_insert f14 (TArrow τ1 τ2) (binder_insert x τ1 Γ)) e τ2 → P P0 Γ (rec: f14 x := e)%MLE (TArrow τ1 τ2))
  → (∀ (P0 : program_env) (Γ : gmap string type) (e1 e2 : expr) (τ1 τ2 : type), P0;; Γ ⊢ₜ e1 : TArrow τ1 τ2 → P P0 Γ e1 (TArrow τ1 τ2) → P0;; Γ ⊢ₜ e2 : τ1 → P P0 Γ e2 τ1 → P P0 Γ (e1 e2) τ2)
  → (∀ (P0 : program_env) (Γ : gmap string type) (e : expr) (τ : type), subst_prog_env (ren (+1)) P0;; subst (ren (+1)) <$> Γ ⊢ₜ e : τ → P (subst_prog_env (ren (+1)) P0) (subst (ren (+1)) <$> Γ) e τ → P P0 Γ (Λ: <>, e)%MLE (TForall τ))
  → (∀ (P0 : program_env) (Γ : gmap string type) (e : expr) (τ τ' : {bind type}), P0;; Γ ⊢ₜ e : TForall τ → P P0 Γ e (TForall τ) → P P0 Γ (TApp e) τ.[τ'/])
  → (∀ (P0 : program_env) (Γ : gmap string type) (e : expr) (τ τ' : type), P0;; Γ ⊢ₜ e : τ.[τ'/] → P P0 Γ e τ.[τ'/] → P P0 Γ (pack:e)%MLE (TExist τ))
  → (∀ (P0 : program_env) (Γ : gmap string type) (x : binder) (e1 e2 : expr) (τ : {bind type}) (τ' : type), P0;; Γ ⊢ₜ e1 : TExist τ → P P0 Γ e1 (TExist τ) → subst_prog_env (ren (+1)) P0;; binder_insert x τ (subst (ren (+1)) <$> Γ) ⊢ₜ e2 : τ'.[ren (+1)] → P (subst_prog_env (ren (+1)) P0) (binder_insert x τ (subst (ren (+1)) <$> Γ)) e2 τ'.[ren (+1)] → P P0 Γ (unpack: x := e1 in e2)%MLE τ')
  → (∀ (P0 : program_env) (Γ : gmap string type) (e : expr) (τ : {bind type}), P0;; Γ ⊢ₜ e : τ.[TRec τ/] → P P0 Γ e τ.[TRec τ/] → P P0 Γ (roll:e)%MLE (TRec τ))
  → (∀ (P0 : program_env) (Γ : gmap string type) (e : expr) (τ : {bind type}), P0;; Γ ⊢ₜ e : TRec τ → P P0 Γ e (TRec τ) → P P0 Γ (unroll:e)%MLE τ.[TRec τ/])
  → (∀ (P0 : program_env) (Γ : gmap string type) (e1 e2 : expr) (τ : type), P0;; Γ ⊢ₜ e1 : TNat → P P0 Γ e1 TNat → P0;; Γ ⊢ₜ e2 : τ → P P0 Γ e2 τ → P P0 Γ (AllocN e1 e2) (TArray τ))
  → (∀ (P0 : program_env) (Γ : gmap string type) (e1 e2 : expr) (τ : type), P0;; Γ ⊢ₜ e1 : TArray τ → P P0 Γ e1 (TArray τ) → P0;; Γ ⊢ₜ e2 : TNat → P P0 Γ e2 TNat → P P0 Γ (LoadN e1 e2) τ)
  → (∀ (P0 : program_env) (Γ : gmap string type) (e1 e2 e3 : expr) (τ : type), P0;; Γ ⊢ₜ e1 : TArray τ → P P0 Γ e1 (TArray τ) → P0;; Γ ⊢ₜ e2 : TNat → P P0 Γ e2 TNat → P0;; Γ ⊢ₜ e3 : τ → P P0 Γ e3 τ → P P0 Γ (StoreN e1 e2 e3) TUnit)
  → (∀ (P0 : program_env) (Γ : gmap string type) (s : string) (el : list expr) (tl : list type) (tr : type), P0 !! s = Some (FunType tl tr) → Forall2 (typed P0 Γ) el tl → Forall2 (P P0 Γ) el tl → P P0 Γ (Extern s el) tr) 
  →  ∀ (P0 : program_env) (Γ : gmap string type) (e : expr) (t : type), P0;; Γ ⊢ₜ e : t → P P0 Γ e t.
Proof.
  do 27 intros ?.
  fix IH 5. intros ????; destruct 1; eauto 5.
  enough (Forall2 (P P0 Γ) el tl) by (eapply H25; clear IH; done).
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

Lemma typed_closed P Γ τ e : P ;; Γ ⊢ₜ e : τ → is_closed_expr (dom Γ) e.
Proof.
  intros H; induction H using typed_ind; cbn; eauto.
  - by eapply bool_decide_pack, elem_of_dom_2.
  - rewrite !dom_binder_insert in IHtyped.
    destruct x, f14; cbn in *; try apply IHtyped.
  - by erewrite dom_fmap_L in IHtyped.
  - rewrite !dom_binder_insert !dom_fmap_L in IHtyped2. eauto.
  - eapply forallb_True, Forall2_Forall_l. 1:done.
    eapply Forall_true. done.
Qed.
Set Elimination Schemes.
End IndDef.

Fixpoint zip_types (an : list binder) (av : list type) : option (gmap string type) := match an, av with
  nil, nil => Some ∅
| (b::ar), (vx::vr) => option_map (binder_insert b vx) (zip_types ar vr)
| _, _ => None end.

Definition fun_typed (P : program_env) (Pt : program_type) (m : ml_function) : Prop := match m, Pt with
  MlFun bs e, FunType ats rt => ∃ Γ', zip_types bs ats = Some Γ' ∧ typed P Γ' e rt end. 

Definition program_typed (P : program_env) (p : ml_program) : Prop := 
  map_Forall (λ s Pt, ∃ m, (p:gmap string _) !! s = Some m ∧ fun_typed P Pt m) (P : gmap string _).


Notation "P ;; Γ ⊢ₜ e : τ" := (typed P Γ e τ) (at level 74, e, τ at next level).
