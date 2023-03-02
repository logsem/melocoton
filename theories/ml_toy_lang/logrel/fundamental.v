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
  Context (P : program_env).
  Notation D := (persistent_predO val (iPropI Σ)).

  Notation "⟦ P ⟧ₚ* x " := (interp_prog_env p P x) (at level 10).
  Notation "⟦ τ ⟧ x " := (interp p τ x) (at level 10).
  Notation "⟦ τ ⟧ₑ x" := (interp_expr p τ x) (at level 10).
  Notation "⟦ Γ ⟧* x" := (interp_env p Γ x) (at level 10).
  Notation "Γ ⊨ e : τ" := (log_typed (p:=p) P Γ e τ) (at level 74, e, τ at next level).

  Lemma interp_expr_bind K e Δ τ τ' :
    ⟦ τ ⟧ₑ Δ e -∗ (∀ v, ⟦ τ ⟧ Δ v -∗ ⟦ τ' ⟧ₑ Δ (fill K (of_val v))) -∗ ⟦ τ' ⟧ₑ Δ (fill K e).
  Proof. iIntros; iApply wp_bind; iApply (wp_wand with "[$]"); done. Qed.

  Lemma sem_typed_var Γ x τ :
    Γ !! x = Some τ → ⊢ Γ ⊨ Var x : τ.
  Proof.
    iIntros (? Δ vs) "!# #HΓ #HP"; simpl.
    iDestruct (interp_env_Some_l with "HΓ") as (v) "[% ?]"; first done.
    rewrite H0.
    iApply wp_value; done.
  Qed.

  Lemma sem_typed_unit Γ : ⊢ Γ ⊨ # LitUnit : TUnit.
  Proof. iIntros (Δ vs) "!# #HΓ #HP". iApply wp_value; done. Qed.

  Lemma sem_typed_nat Γ (n:Z) : ⊢ Γ ⊨ # n : TNat.
  Proof. iIntros (Δ vs) "!# #HΓ #HP /=". iApply wp_value; eauto. Qed.

  Lemma sem_typed_bool Γ (b:bool) : ⊢ Γ ⊨ # b : TBool.
  Proof. iIntros (Δ vs) "!# #HΓ #HP /=". iApply wp_value; eauto. Qed.

  

  Lemma sem_typed_nat_binop Γ op e1 e2 :
    binop_arithmetic op = true →
    Γ ⊨ e1 : TNat -∗ Γ ⊨ e2 : TNat -∗ Γ ⊨ BinOp op e1 e2 : TNat.
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

  Lemma sem_typed_pair Γ e1 e2 τ1 τ2 : Γ ⊨ e1 : τ1 -∗ Γ ⊨ e2 : τ2 -∗ Γ ⊨ Pair e1 e2 : TProd τ1 τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [PairLCtx _]); first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iApply (interp_expr_bind [PairRCtx _]); first by iApply "IH2".
    iIntros (w) "#Hw/=".
    iApply wp_value; simpl; eauto.
  Qed.

  Lemma sem_typed_fst Γ e τ1 τ2 : Γ ⊨ e : TProd τ1 τ2 -∗ Γ ⊨ Fst e : τ1.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [FstCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
    iApply wp_pure_step_later; [done|]; iIntros "!> _". by iApply wp_value.
  Qed.

  Lemma sem_typed_snd Γ e τ1 τ2 : Γ ⊨ e : TProd τ1 τ2 -∗ Γ ⊨ Snd e : τ2.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [SndCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
    iApply wp_pure_step_later; [done|]; iIntros "!> _". by iApply wp_value.
  Qed.

  Lemma sem_typed_injl Γ e τ1 τ2 : Γ ⊨ e : τ1 -∗ Γ ⊨ InjL e : (TSum τ1 τ2).
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [InjLCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_value; simpl; eauto.
  Qed.

  Lemma sem_typed_injr Γ e τ1 τ2 : Γ ⊨ e : τ2 -∗ Γ ⊨ InjR e : TSum τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [InjRCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_value; simpl; eauto.
  Qed.

  Lemma sem_typed_case Γ e0 e1 e2 τ1 τ2 τ3 :
    Γ ⊨ e0: TSum τ1 τ2 -∗
    τ1 :: Γ ⊨ e1 : τ3 -∗
    τ2 :: Γ ⊨ e2 : τ3 -∗
    Γ ⊨ Case e0 e1 e2 : τ3.
  Proof.
    iIntros "#IH1 #IH2 #IH3" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [CaseCtx _ _]); first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as (w) "[% Hw]"; simplify_eq/=.
    + iApply wp_pure_step_later; auto 1 using to_of_val; asimpl. iIntros "!> _".
      iApply ("IH2" $! Δ (w :: vs)). iApply interp_env_cons; auto.
    + iApply wp_pure_step_later; auto 1 using to_of_val; asimpl. iIntros "!> _".
      iApply ("IH3" $! Δ (w :: vs)). iApply interp_env_cons; auto.
  Qed.

  Lemma sem_typed_if Γ e0 e1 e2 τ :
    Γ ⊨ e0 : TBool -∗ Γ ⊨ e1 : τ -∗ Γ ⊨ e2 : τ -∗ Γ ⊨ If e0 e1 e2 : τ.
  Proof.
    iIntros "#IH1 #IH2 #IH3" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [IfCtx _ _]); first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iDestruct "Hv" as ([]) "%"; subst; simpl;
      [iApply wp_pure_step_later .. ]; auto; iIntros "!> _";
        [iApply "IH2"| iApply "IH3"]; auto.
  Qed.

  Lemma sem_typed_rec Γ e τ1 τ2 :
    TArrow τ1 τ2 :: τ1 :: Γ ⊨ e : τ2 -∗ Γ ⊨ Rec e : TArrow τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply wp_value. simpl. iModIntro. iLöb as "IHL". iIntros (w) "#Hw".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iIntros "!> _".
    asimpl. change (Rec _) with (of_val (RecV e.[upn 2 (env_subst vs)])) at 2.
    iApply ("IH" $! Δ (_ :: w :: vs)).
    iApply interp_env_cons; iSplit; [|iApply interp_env_cons]; auto.
  Qed.

  Lemma sem_typed_lam Γ e τ1 τ2 : τ1 :: Γ ⊨ e : τ2 -∗ Γ ⊨ Lam e : TArrow τ1 τ2.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply wp_value. simpl. iModIntro. iIntros (w) "#Hw".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iIntros "!> _".
    asimpl.
    iApply ("IH" $! Δ (w :: vs)); auto.
    iApply interp_env_cons; iSplit; auto.
  Qed.

  Lemma sem_typed_letin Γ e1 e2 τ1 τ2 : Γ ⊨ e1 : τ1 -∗ τ1 :: Γ ⊨ e2 : τ2 -∗ Γ ⊨ LetIn e1 e2: τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [LetInCtx _]); first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iIntros "!> _".
    asimpl. iApply ("IH2" $! Δ (v :: vs)).
    iApply interp_env_cons; iSplit; eauto.
  Qed.

  Lemma sem_typed_seq Γ e1 e2 τ1 τ2 : Γ ⊨ e1 : τ1 -∗ Γ ⊨ e2 : τ2 -∗ Γ ⊨ Seq e1 e2 : τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [SeqCtx _]); first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iApply wp_pure_step_later; auto 1 using to_of_val. iIntros "!> _".
    iApply "IH2"; done.
  Qed.

  Lemma sem_typed_app Γ e1 e2 τ1 τ2 : Γ ⊨ e1 : TArrow τ1 τ2 -∗ Γ ⊨ e2 : τ1 -∗ Γ ⊨ App e1 e2 :  τ2.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ #HP"; simpl.
    iApply (interp_expr_bind [AppLCtx _]); first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iApply (interp_expr_bind [AppRCtx _]); first by iApply "IH2".
    iIntros (w) "#Hw/=".
    iApply "Hv"; done.
  Qed.

  Lemma sem_typed_tlam Γ e τ : (subst (ren (+1)) <$> Γ) ⊨ e : τ -∗ Γ ⊨ TLam e : TForall τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply wp_value; simpl.
    iModIntro; iIntros (τi). iApply wp_pure_step_later; auto. iIntros "!> _".
    iApply "IH". by iApply interp_env_ren.
  Qed.

  Lemma sem_typed_tapp Γ e τ τ' : Γ ⊨ e : TForall τ -∗ Γ ⊨ TApp e : τ.[τ'/].
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [TAppCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_wand_r; iSplitL;
      [iApply ("Hv" $! (⟦ τ' ⟧ Δ)); iPureIntro; apply _|]; cbn.
    iIntros (w) "?". by iApply interp_subst.
  Qed.

  Lemma sem_typed_pack Γ e τ τ' : Γ ⊨ e : τ.[τ'/] -∗ Γ ⊨ Pack e : TExist τ.
  Proof.
    iIntros "#IH" (Δ vs) "!##HΓ /=".
    iApply (interp_expr_bind [PackCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_value.
    rewrite -interp_subst.
    iExists (interp _ Δ), _; iSplit; done.
  Qed.

  Lemma sem_typed_unpack Γ e1 e2 τ τ' :
    Γ ⊨ e1 : TExist τ -∗
    τ :: (subst (ren (+1)) <$> Γ) ⊨ e2 : τ'.[ren (+1)]  -∗
    Γ ⊨ UnpackIn e1 e2 : τ'.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [UnpackInCtx _]); first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iDestruct "Hv" as (τi w ->) "#Hw"; simpl.
    iApply wp_pure_step_later; auto 1 using to_of_val. iIntros "!> _".
    asimpl.
    iApply wp_wand_r; iSplitL.
    { iApply ("IH2" $! (τi :: Δ) (w :: vs) with "[]").
      iApply interp_env_cons; iSplit; first done.
      iApply interp_env_ren; done. }
    iIntros (u) "Hu".
    iApply (interp_weaken [] [_]); done.
  Qed.

  Lemma sem_typed_fold Γ e τ : Γ ⊨ e : τ.[(TRec τ)/] -∗ Γ ⊨ Fold e : TRec τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [FoldCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_value.
    rewrite /= -interp_subst fixpoint_interp_rec1_eq /=.
    iModIntro; eauto.
  Qed.

  Lemma sem_typed_unfold Γ e τ : Γ ⊨ e : TRec τ -∗ Γ ⊨ Unfold e : τ.[(TRec τ)/].
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [UnfoldCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    rewrite /= fixpoint_interp_rec1_eq.
    change (fixpoint _) with (⟦ TRec τ ⟧ Δ); simpl.
    iDestruct "Hv" as (w) "#[% Hw]"; subst.
    iApply wp_pure_step_later; cbn; auto using to_of_val.
    iIntros "!> _". iApply wp_value. by iApply interp_subst.
  Qed.

  Lemma sem_typed_fork Γ e : Γ ⊨ e : TUnit -∗ Γ ⊨ Fork e : TUnit.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply wp_fork. rewrite -bi.later_sep. iNext; iSplitL; trivial.
    iApply wp_wand_l. iSplitL; [|iApply "IH"; auto]; auto.
  Qed.

  Lemma sem_typed_alloc Γ e τ : Γ ⊨ e : τ -∗ Γ ⊨ Alloc e : Tref τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [AllocCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_fupd.
    iApply wp_alloc; auto 1 using to_of_val.
    iNext; iIntros (l) "Hl /=".
    iMod (inv_alloc _ with "[Hl]") as "HN";
      [| iModIntro; iExists _; iSplit; trivial]; eauto.
  Qed.

  Lemma sem_typed_load Γ e τ : Γ ⊨ e : (Tref τ) -∗ Γ ⊨ Load e : τ.
  Proof.
    iIntros "#IH" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [LoadCtx]); first by iApply "IH".
    iIntros (v) "#Hv /=".
    iDestruct "Hv" as (l) "[% #Hv]"; subst.
    iApply wp_atomic.
    iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
    iApply (wp_load with "Hw1").
    iModIntro. iNext.
    iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
  Qed.

  Lemma sem_typed_store Γ e1 e2 τ : Γ ⊨ e1 : (Tref τ) -∗ Γ ⊨ e2 : τ -∗ Γ ⊨ Store e1 e2 : TUnit.
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
  Qed.

  Lemma sem_typed_CAS Γ e1 e2 e3 τ :
    EqType τ →
    Γ ⊨ e1 : Tref τ -∗
    Γ ⊨ e2 : τ -∗
    Γ ⊨ e3 : τ -∗
    Γ ⊨ CAS e1 e2 e3 : TBool.
  Proof.
    iIntros (Heqτ) "#IH1 #IH2 #IH3".
    iIntros (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [CasLCtx _ _]); first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (interp_expr_bind [CasMCtx _ _]); first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    iApply (interp_expr_bind [CasRCtx _ _]); first by iApply "IH3".
    iIntros (v3) "#Hv3 /=".
    iDestruct "Hv1" as (l) "[% Hv1]"; subst.
    iApply wp_atomic.
    iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
    destruct (decide (v2 = w)) as [|Hneq]; subst.
    + iApply (wp_cas_suc with "Hw1"); auto using to_of_val.
      iModIntro. iNext.
      iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
    + iApply (wp_cas_fail with "Hw1"); auto using to_of_val.
      iModIntro. iNext.
      iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
  Qed.

  Lemma sem_typed_FAA Γ e1 e2 : Γ ⊨ e1 : Tref TNat -∗ Γ ⊨ e2 : TNat -∗ Γ ⊨ FAA e1 e2 : TNat.
  Proof.
    iIntros "#IH1 #IH2" (Δ vs) "!# #HΓ #HP /=".
    iApply (interp_expr_bind [FAALCtx _]); first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (interp_expr_bind [FAARCtx _]); first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    iDestruct "Hv1" as (l) "[% Hv1]".
    iDestruct "Hv2" as (k) "%"; simplify_eq/=.
    iApply wp_atomic.
    iInv (logN .@ l) as (w) "[Hw1 #>Hw2]" "Hclose".
    iDestruct "Hw2" as (m) "%"; simplify_eq/=.
    iApply (wp_FAA with "Hw1"); auto using to_of_val.
    iModIntro. iNext.
    iIntros "Hw1".
    iMod ("Hclose" with "[Hw1]"); last by eauto.
    iNext; iExists _; iFrame. by eauto.
  Qed.

  Theorem fundamental Γ e τ : Γ ⊢ₜ e : τ → ⊢ Γ ⊨ e : τ.
  Proof.
    induction 1.
    - iApply sem_typed_var; done.
    - iApply sem_typed_unit; done.
    - iApply sem_typed_nat; done.
    - iApply sem_typed_bool; done.
    - iApply sem_typed_nat_binop; done.
    - iApply sem_typed_pair; done.
    - iApply sem_typed_fst; done.
    - iApply sem_typed_snd; done.
    - iApply sem_typed_injl; done.
    - iApply sem_typed_injr; done.
    - iApply sem_typed_case; done.
    - iApply sem_typed_if; done.
    - iApply sem_typed_rec; done.
    - iApply sem_typed_lam; done.
    - iApply sem_typed_letin; done.
    - iApply sem_typed_seq; done.
    - iApply sem_typed_app; done.
    - iApply sem_typed_tlam; done.
    - iApply sem_typed_tapp; done.
    - iApply sem_typed_pack; done.
    - iApply sem_typed_unpack; done.
    - iApply sem_typed_fold; done.
    - iApply sem_typed_unfold; done.
    - iApply sem_typed_fork; done.
    - iApply sem_typed_alloc; done.
    - iApply sem_typed_load; done.
    - iApply sem_typed_store; done.
    - iApply sem_typed_CAS; done.
    - iApply sem_typed_FAA; done.
  Qed.
End typed_interp.
