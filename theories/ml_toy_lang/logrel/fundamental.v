From iris.base_logic Require Import invariants.
From melocoton.language Require Import lifting.
From iris.proofmode Require Import proofmode.
From melocoton.ml_toy_lang.logrel Require Export logrel typing.
From Autosubst Require Export Autosubst.
From iris.prelude Require Import options.

Definition log_typed `{!heapGS_ML Σ, !invGS_gen hlc Σ} {p:prog_environ ML_lang Σ} (P : program_env) (Γ : gmap string type) (e : expr) (τ : type) : iProp Σ :=
  □ ∀ Δ vs, ⟦ Γ ⟧* p Δ vs -∗ ⟦ P ⟧ₚ* p Δ -∗ ⟦ τ ⟧ₑ p Δ (env_subst vs e).
Notation "P ; Γ ⊨ e : τ" := (log_typed P Γ e τ) (at level 74, Γ, e, τ at next level).


Section typed_interp.
  Context `{!heapGS_ML Σ, !invGS_gen hlc Σ}.
  Context {p:prog_environ ML_lang Σ}.
  Notation D := (persistent_predO val (iPropI Σ)).

  Notation "⟦ P ⟧ₚ* x " := (interp_prog_env p P x) (at level 10).
  Notation "⟦ τ ⟧ x " := (interp p τ x) (at level 10).
  Notation "⟦ τ ⟧ₑ x" := (interp_expr p τ x) (at level 10).
  Notation "⟦ Γ ⟧* x" := (interp_env p Γ x) (at level 10).
  Notation "P ; Γ ⊨ e : τ" := (log_typed (p:=p) P Γ e τ) (at level 74, Γ, e, τ at next level).

  Lemma interp_expr_bind K e Δ τ τ' :
    ⟦ τ ⟧ₑ Δ e -∗ (∀ v, ⟦ τ ⟧ Δ v -∗ ⟦ τ' ⟧ₑ Δ (fill K (of_val v))) -∗ ⟦ τ' ⟧ₑ Δ (fill K e).
  Proof. iIntros; iApply wp_bind; iApply (wp_wand with "[$]"); done. Qed.

  Lemma sem_typed_var P Γ x τ :
    Γ !! x = Some τ → ⊢ P ; Γ ⊨ Var x : τ.
  Proof.
    iIntros (? Δ vs) "!# #HΓ #HP"; simpl.
    iDestruct (interp_env_Some_l with "HΓ") as (v) "[% ?]"; first done.
    rewrite H0.
    iApply wp_value; done.
  Qed.

  Lemma sem_typed_unit P Γ : ⊢ P ; Γ ⊨ # LitUnit : TUnit.
  Proof. iIntros (Δ vs) "!# #HΓ #HP". iApply wp_value; done. Qed.

  Lemma sem_typed_nat P Γ (n:Z) : ⊢ P ; Γ ⊨ # n : TNat.
  Proof. iIntros (Δ vs) "!# #HΓ #HP /=". iApply wp_value; eauto. Qed.

  Lemma sem_typed_bool P Γ (b:bool) : ⊢ P ; Γ ⊨ # b : TBool.
  Proof. iIntros (Δ vs) "!# #HΓ #HP /=". iApply wp_value; eauto. Qed.

  Lemma sem_typed_nat_binop P Γ op e1 e2 :
    binop_arithmetic op = true →
    P ; Γ ⊨ e1 : TNat -∗ P ; Γ ⊨ e2 : TNat -∗ P ; Γ ⊨ BinOp op e1 e2 : TNat.
  Proof.
    iIntros (Hop) "#IH1 #IH2". iIntros (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [BinOpRCtx _ _]); first by iApply "IH2".
    iIntros (v) "#Hv /=".
    iApply (interp_expr_bind [BinOpLCtx _ _]); first by iApply "IH1".
    iIntros (w) "#Hw/=".
    iDestruct "Hv" as (n) "%"; iDestruct "Hw" as (n') "%"; simplify_eq/=.
    assert (exists (nr:Z), bin_op_eval op (#n') (#n) = Some (#nr)) as [nr Hnr].
    1: { destruct op. 1-10: by eexists. all: cbn in Hop; done. }
    iApply wp_pure_step_later; [done|]; iIntros "!>". iApply wp_value; first done.
    by iExists _.
  Qed.

  Lemma sem_typed_nat_binop_bool P Γ op e1 e2 :
    binop_arithmetic_to_bool op = true →
    P ; Γ ⊨ e1 : TNat -∗ P ; Γ ⊨ e2 : TNat -∗ P ; Γ ⊨ BinOp op e1 e2 : TBool.
  Proof.
    iIntros (Hop) "#IH1 #IH2". iIntros (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [BinOpRCtx _ _]); first by iApply "IH2".
    iIntros (v) "#Hv /=".
    iApply (interp_expr_bind [BinOpLCtx _ _]); first by iApply "IH1".
    iIntros (w) "#Hw/=".
    iDestruct "Hv" as (n) "%"; iDestruct "Hw" as (n') "%"; simplify_eq/=.
    assert (exists (r:bool), bin_op_eval op (#n') (#n) = Some (#r)) as [b Hb].
    1: { destruct op. 1-10,13: cbn in Hop; done.
         all: unfold bin_op_eval; destruct decide; simplify_eq.
         all: cbn; destruct bool_decide; by eexists. }
    iApply wp_pure_step_later; [done|]; iIntros "!>". iApply wp_value; first done.
    by iExists _.
  Qed.

  Lemma sem_typed_bool_binop P Γ op e1 e2 :
    binop_boolish op = true →
    P ; Γ ⊨ e1 : TBool -∗ P ; Γ ⊨ e2 : TBool -∗ P ; Γ ⊨ BinOp op e1 e2 : TBool.
  Proof.
    iIntros (Hop) "#IH1 #IH2". iIntros (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [BinOpRCtx _ _]); first by iApply "IH2".
    iIntros (v) "#Hv /=".
    iApply (interp_expr_bind [BinOpLCtx _ _]); first by iApply "IH1".
    iIntros (w) "#Hw/=".
    iDestruct "Hv" as (b) "%"; iDestruct "Hw" as (b') "%"; simplify_eq/=.
    assert (exists (r:bool), bin_op_eval op (#b') (#b) = Some (#r)) as [br Hbr].
    1: { destruct op. all: cbn in Hop; try done.
         all: unfold bin_op_eval; destruct decide; simplify_eq.
         all: by eexists. }
    iApply wp_pure_step_later; [done|]; iIntros "!>". iApply wp_value; first done.
    by iExists _.
  Qed.

  Lemma sem_typed_eq P Γ τ e1 e2 :
    EqType τ →
    P ; Γ ⊨ e1 : τ -∗ P ; Γ ⊨ e2 : τ -∗ P ; Γ ⊨ BinOp EqOp e1 e2 : TBool.
  Proof.
    iIntros (Hop) "#IH1 #IH2". iIntros (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [BinOpRCtx _ _]); first by iApply "IH2".
    iIntros (v) "#Hv /=".
    iApply (interp_expr_bind [BinOpLCtx _ _]); first by iApply "IH1".
    iIntros (w) "#Hw/=". inversion Hop. all: cbn.
    1: iDestruct "Hv" as "%"; iDestruct "Hw" as "%"; simplify_eq/=.
    2,3: iDestruct "Hv" as (v1) "%"; iDestruct "Hw" as (v2) "%"; simplify_eq/=.
    4: iDestruct "Hv" as (v1) "[% #H1]"; iDestruct "Hw" as (v2) "[% #H2]"; simplify_eq/=.
    all: iApply wp_pure_step_later; first by left.
    all: iIntros "!>"; iApply wp_value; first done.
    all: by iExists _.
  Qed.

  Lemma sem_typed_pair P Γ e1 e2 τ1 τ2 : P ; Γ ⊨ e1 : τ1 -∗ P ; Γ ⊨ e2 : τ2 -∗ P ; Γ ⊨ Pair e1 e2 : TProd τ1 τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [PairRCtx _]); first by iApply "IH2".
    iIntros (v) "#Hv /=".
    iApply (interp_expr_bind [PairLCtx _]); first by iApply "IH1".
    iIntros (w) "#Hw/=".
    iApply wp_pure_step_later; first done. iIntros "!>".
    iApply wp_value; simpl; eauto.
  Qed.

  Lemma sem_typed_fst P Γ e τ1 τ2 : P ; Γ ⊨ e : TProd τ1 τ2 -∗ P ; Γ ⊨ Fst e : τ1.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [FstCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
    iApply wp_pure_step_later; [done|]; iIntros "!>". by iApply wp_value.
  Qed.

  Lemma sem_typed_snd P Γ e τ1 τ2 : P ; Γ ⊨ e : TProd τ1 τ2 -∗ P ; Γ ⊨ Snd e : τ2.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [SndCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
    iApply wp_pure_step_later; [done|]; iIntros "!>". by iApply wp_value.
  Qed.

  Lemma sem_typed_injl P Γ e τ1 τ2 : P ; Γ ⊨ e : τ1 -∗ P ; Γ ⊨ InjL e : (TSum τ1 τ2).
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [InjLCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_pure_step_later; first done. iIntros "!>".
    iApply wp_value; simpl; eauto.
  Qed.

  Lemma sem_typed_injr P Γ e τ1 τ2 : P ; Γ ⊨ e : τ2 -∗ P ; Γ ⊨ InjR e : TSum τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [InjRCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_pure_step_later; first done. iIntros "!>".
    iApply wp_value; simpl; eauto.
  Qed.

  Lemma sem_typed_case P Γ e0 e1 e2 τ1 τ2 τ3 :
    P ; Γ ⊨ e0: TSum τ1 τ2 -∗
    P ; Γ ⊨ e1 : (TArrow τ1 τ3) -∗
    P ; Γ ⊨ e2 : (TArrow τ2 τ3) -∗
    P ; Γ ⊨ Case e0 e1 e2 : τ3.
  Proof.
    iIntros "#IH1 #IH2 #IH3" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [CaseCtx _ _]); first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as (w) "[% Hw]"; simplify_eq/=.
    + iApply wp_pure_step_later; auto 1 using to_of_val; asimpl. iIntros "!>".
      iPoseProof ("IH2" $! Δ vs with "HΓ HP") as "IH".
      iApply (interp_expr_bind [AppLCtx _]); first by iApply "IH".
      iIntros (v) "#Hv". by iApply "Hv".
    + iApply wp_pure_step_later; auto 1 using to_of_val; asimpl. iIntros "!>".
      iPoseProof ("IH3" $! Δ vs with "HΓ HP") as "IH".
      iApply (interp_expr_bind [AppLCtx _]); first by iApply "IH".
      iIntros (v) "#Hv". by iApply "Hv".
  Qed.

  Lemma sem_typed_if P Γ e0 e1 e2 τ :
    P ; Γ ⊨ e0 : TBool -∗ P ; Γ ⊨ e1 : τ -∗ P ; Γ ⊨ e2 : τ -∗ P ; Γ ⊨ If e0 e1 e2 : τ.
  Proof.
    iIntros "#IH1 #IH2 #IH3" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [IfCtx _ _]); first by iApply "IH1".
    iIntros (v) "(%&->) /=". destruct b;
    (iApply wp_pure_step_later; first done); iIntros "!>";
      [iApply "IH2"| iApply "IH3"]; auto.
  Qed.

  (* TODO should go to stdpp *)
  Lemma binder_delete_binder_delete {A} (b1:binder) (b2:binder) (m:gmap string A) : 
    binder_delete b1 (binder_delete b2 m) = binder_delete b2 (binder_delete b1 m).
  Proof.
    destruct b1; cbn; try done.
    by rewrite binder_delete_delete.
  Qed.

  Lemma sem_typed_rec P Γ f x e τ1 τ2 :
    P ; (binder_insert f (TArrow τ1 τ2) (binder_insert x τ1 Γ)) ⊨ e : τ2 -∗ P ; Γ ⊨ Rec f x e : TArrow τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply wp_pure_step_later; first done; iIntros "!>".
    iApply wp_value; first done. iLöb as "IHL". cbn.
    iIntros "!> %v #Hv".
    iApply wp_pure_step_later; first done; iIntros "!>".
    rewrite (binder_delete_binder_delete f x) /env_subst -(subst_all_binder_insert_2).
    iApply ("IH" $! Δ with "[HΓ] HP").
    iApply (interp_env_binder_insert_2 with "[IHL] [-]"); first iApply "IHL".
    iApply (interp_env_binder_insert_2 with "Hv HΓ").
  Qed.

  Lemma sem_typed_app P Γ e1 e2 τ1 τ2 : P ; Γ ⊨ e1 : TArrow τ1 τ2 -∗ P ; Γ ⊨ e2 : τ1 -∗ P ; Γ ⊨ App e1 e2 :  τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [AppRCtx _]); first by iApply "IH2".
    iIntros (v) "#Hv /=".
    iApply (interp_expr_bind [AppLCtx _]); first by iApply "IH1".
    cbn. iIntros (w) "#Hw/=".
    iApply "Hw"; done.
  Qed.

  Lemma sem_typed_tlam P Γ e τ : subst_prog_env (ren (+1)) P ; (subst (ren (+1)) <$> Γ) ⊨ e : τ -∗ P ; Γ ⊨ TLam e : TForall τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply wp_pure_step_later; first done; iIntros "!>".
    iApply wp_value; first done. cbn.
    iModIntro; iIntros (τi).
    iApply wp_pure_step_later; first done. iIntros "!>". cbn.
    iApply "IH". 1: by iApply interp_env_ren.
    by iApply interp_prog_env_ren.
  Qed.

  Lemma sem_typed_tapp P Γ e τ τ' : P ; Γ ⊨ e : TForall τ -∗ P ; Γ ⊨ TApp e : τ.[τ'/].
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [AppLCtx _]); first by iApply "IH". cbn.
    iIntros (v) "#Hv /=".
    iApply wp_wand_r; iSplitL;
      [iApply ("Hv" $! (⟦ τ' ⟧ Δ)); iPureIntro; apply _|]; cbn.
    iIntros (w) "?". by iApply interp_subst.
  Qed.

  Lemma sem_typed_pack P Γ e τ τ' : P ; Γ ⊨ e : τ.[τ'/] -∗ P ; Γ ⊨ Pack e : TExist τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    rewrite -interp_subst.
    iExists (interp _ _ Δ), _; iSplit; done.
  Qed.

  Lemma sem_typed_unpack P Γ x e1 e2 τ τ' :
    P ; Γ ⊨ e1 : TExist τ -∗
    subst_prog_env (ren (+1)) P ; binder_insert x τ (subst (ren (+1)) <$> Γ) ⊨ e2 : τ'.[ren (+1)]  -∗
    P ; Γ ⊨ UnpackIn x e1 e2 : τ'.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [AppRCtx _]); first by iApply "IH1". cbn.
    iIntros (v) "#(%τi & %vv & -> & Hv) /=".
    iApply (wp_bind [AppLCtx _]); first iApply (wp_wand _ _ _ (λ v, ⌜v = (λ: x, env_subst (delete_binder vs x) e2)%V⌝)%I).
    1: iApply wp_pure_step_later; first done; iIntros "!>". 1: iApply wp_value; first done; iPureIntro; done.
    iIntros (?) "->". cbn.
    iApply wp_pure_step_later; first done. iIntros "!>". cbn.
    rewrite -subst_all_binder_insert.
    iApply wp_wand_r; iSplitL.
    { iApply ("IH2" $! (τi :: Δ) with "[]").
      1: iApply interp_env_binder_insert_2; first iApply "Hv".
      1: iApply interp_env_ren; done.
      1: iApply interp_prog_env_ren; done. }
    iIntros (u) "Hu".
    iApply (interp_weaken _ [] [_]); done.
  Qed.

  Lemma sem_typed_fold P Γ e τ : P ; Γ ⊨ e : τ.[(TRec τ)/] -∗ P ; Γ ⊨ Roll e : TRec τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [AppRCtx _]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_pure_step_later; first done; iIntros "!>"; cbn.
    rewrite lookup_singleton.
    iApply wp_value; first done.
    rewrite /= -interp_subst fixpoint_interp_rec1_eq /=.
    iModIntro; eauto.
  Qed.

  Lemma sem_typed_unfold P Γ e τ : P ; Γ ⊨ e : TRec τ -∗ P ; Γ ⊨ Unroll e : τ.[(TRec τ)/].
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [AppRCtx _]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    rewrite /= fixpoint_interp_rec1_eq.
    change (fixpoint _) with (⟦ TRec τ ⟧ Δ); simpl.
    iDestruct "Hv" as (w) "#[% Hw]"; subst.
    iApply wp_pure_step_later; cbn; auto using to_of_val. rewrite lookup_singleton.
    iIntros "!>". iApply wp_value; first done. by iApply interp_subst.
  Qed.

  Lemma sem_typed_alloc P Γ e τ : P ; Γ ⊨ e : τ -∗ P ; Γ ⊨ Alloc e : Tref τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [AllocNRCtx _]); first by iApply "IH".
    iIntros (v) "#Hv /=". unfold interp_expr.
    wp_alloc l as "Hl".
    iMod (inv_alloc _ with "[Hl]") as "#HN".
    2: iModIntro; cbn; iExists l; by iSplit.
    iNext; iExists _; by iFrame.
  Qed.

(* TODO: figure out invariants

  Lemma sem_typed_load P Γ e τ : P ; Γ ⊨ e : (Tref τ) -∗ P ; Γ ⊨ Load e : τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [LoadNLCtx _]); first by iApply "IH".
    rewrite /= /fill /=.
    iIntros (v) "#(%l&->&#Hv) /=".
    Search inv.
    iApply wp_atomic.
    iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
    iApply (wp_load with "Hw1").
    iModIntro. iNext.
    iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
  Qed.

  Lemma sem_typed_store Γ e1 e2 τ : P ; Γ ⊨ e1 : (Tref τ) -∗ P ; Γ ⊨ e2 : τ -∗ P ; Γ ⊨ Store e1 e2 : TUnit.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [StoreLCtx _]); first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iApply (interp_expr_bind [StoreRCtx _]); first by iApply "IH2".
    iIntros (w) "#Hw/=".
    iDestruct "Hv" as (l) "[% #Hv]"; subst.
    iApply wp_atomic.
    iInv (logN .@ l) as (z) "[Hz1 #Hz2]" "Hclose".
    iApply (wp_store with "Hz1"); auto using to_of_val.
    iModIntro. iNext.
    iIntros "Hz1". iMod ("Hclose" with "[Hz1 Hz2]"); eauto.
  Qed. *)

  Lemma sem_typed_extern_ind P Γ Δ vs s tr tl1 tl2 vl1 el2 :
      P !! s = Some (FunType (tl1 ++ tl2) tr) →
      ⟦ Γ ⟧* Δ vs -∗ ⟦ P ⟧ₚ* Δ -∗
      ⌜Forall2 (λ e τ, ⊢ P; Γ ⊨ e : τ) el2 tl2⌝ -∗
      ([∗ list] k↦τ;v ∈ tl1;vl1, ⟦ τ ⟧ Δ v) -∗
      (⟦ tr ⟧ₑ Δ) (Extern s (map Val vl1 ++ map (env_subst vs) el2)).
  Proof.
    iIntros (HPs) "#HΓ #HP %H2 #H1".
    iInduction el2 as [|e el2] "IH" forall (vl1 tl1 tl2 HPs H2) "H1".
    - cbn. rewrite app_nil_r. eapply Forall2_nil_inv_l in H2 as ->.
      rewrite app_nil_r in HPs.
      iPoseProof (big_sepM_lookup with "HP") as "#HPs"; first exact HPs. cbn.
      iApply ("HPs" $! s vl1 (⟦ tr ⟧ Δ)).
      iSplitR; first done.
      iSplitL; last by iIntros (r) "Hr".
      iApply "H1".
    - eapply Forall2_cons_inv_l in H2 as (τ&tl2'&Heτ&H2&->).
      cbn. iPoseProof Heτ as "Heτ"; clear Heτ.
      iApply (interp_expr_bind [ExternCtx s vl1 _]); first by iApply "Heτ".
      iIntros (v) "#Hv"; cbn.
      rewrite cons_middle app_assoc -(map_last Val vl1 v).
      rewrite cons_middle app_assoc in HPs.
      iApply "IH".
      + iPureIntro; exact HPs.
      + done.
      + iIntros "!>". iApply (big_sepL2_snoc); iFrame "Hv H1".
  Qed.

  Lemma sem_typed_extern P Γ s el tl tr :
      P !! s = Some (FunType tl tr) →
      ⌜Forall2 (λ e τ, ⊢ P ; Γ ⊨ e : τ) el tl⌝ -∗
      P ; Γ ⊨ (Extern s el) : tr.
  Proof.
    iIntros (Hlu HH Δ vs) "!# #HΓ #HP /=".
    iApply (sem_typed_extern_ind P Γ Δ vs s tr [] tl [] el).
    - done.
    - done.
    - done.
    - iPureIntro; done.
    - done.
  Qed.

  Theorem fundamental P Γ e τ : typed P Γ e τ → ⊢ P ; Γ ⊨ e : τ.
  Proof.
    induction 1.
    - iApply sem_typed_var; done.
    - iApply sem_typed_unit; done.
    - iApply sem_typed_nat; done.
    - iApply sem_typed_bool; done.
    - iApply sem_typed_nat_binop; done.
    - iApply sem_typed_nat_binop_bool; done.
    - iApply sem_typed_bool_binop; done.
    - iApply sem_typed_eq; done.
    - iApply sem_typed_pair; done.
    - iApply sem_typed_fst; done.
    - iApply sem_typed_snd; done.
    - iApply sem_typed_injl; done.
    - iApply sem_typed_injr; done.
    - iApply sem_typed_case; done.
    - iApply sem_typed_if; done.
    - iApply sem_typed_rec; done.
    - iApply sem_typed_app; done.
    - iApply sem_typed_tlam; done.
    - iApply sem_typed_tapp; done.
    - iApply sem_typed_pack; done.
    - iApply sem_typed_unpack; done.
    - iApply sem_typed_fold; done.
    - iApply sem_typed_unfold; done.
    - iApply sem_typed_alloc; done.
    - admit.
    - admit.
    - iApply sem_typed_extern; done.
  Admitted.
End typed_interp.
