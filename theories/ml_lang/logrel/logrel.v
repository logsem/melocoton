From iris.proofmode Require Import proofmode.
From melocoton.ml_lang.logrel Require Export persistent_pred typing iterup.
From melocoton.ml_lang Require Export proofmode.
From melocoton.ml_lang Require Export lang notation metatheory.
From iris.algebra Require Import list gmap big_op.
From transfinite.base_logic.lib Require Import na_invariants ghost_var.
From iris.prelude Require Import options.
From melocoton.language Require Export weakestpre.
From Autosubst Require Export Autosubst.
Import uPred.

(** interp : is a unary logical relation. *)

Class logrelG `{SI: indexT} (Σ : gFunctors) := LogrelG {
  logrel_na_invG :> na_invG Σ;
  wrapperG_addrmapG :> ghost_varG Σ (leibnizO (list val));
  logrel_nais : na_inv_pool_name;
}.

Class logrelGpre `{SI: indexT} (Σ : gFunctors) := {
  logrel_na_invG_pre :> na_invG Σ;
  wrapperG_addrmapG_pre :> ghost_varG Σ (leibnizO (list val));
}.

Definition logrelΣ {SI: indexT} : gFunctors :=
  #[na_invΣ; ghost_varΣ (leibnizO (list val))].

Global Instance subG_logrelΣ_logrelGpre `{SI: indexT} Σ :
  subG logrelΣ Σ → logrelGpre Σ.
Proof. solve_inG. Qed.

Notation na_tok := (na_own logrel_nais ⊤).

Section logrel.
  Context `{SI: indexT}.
  Context {Σ : gFunctors}.
  Context `{!heapG_ML Σ, !invG Σ, !logrelG Σ}.
  Notation D := (persistent_predO val (iPropI Σ)).
  Implicit Types τi  : D.
  Implicit Types Δ : listO D.
  Implicit Types interp : listO D -n> D.

  Local Arguments ofe_car !_.

  Context (T : prog_environ ML_lang Σ).
  Notation "'WP' e {{ Φ } }" := (wp T ⊤ e%E Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'WP' e {{ o , Q } }" := (wp T ⊤ e%E (λ o, Q))
    (at level 20, e, Q at level 200,
     format "'[hv' 'WP'  e  '/' {{  '[' o ,  '/' Q  ']' } } ']'") : bi_scope.
  Notation of_val w := (of_val ML_lang w%V).
  Notation of_outcome w := (of_outcome ML_lang w%V).

  Program Definition env_lookup (x : nat) : listO D -n> D :=
    λne Δ, default (inhabitant : persistent_pred _ _) (Δ !! x).
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Definition interp_unit : listO D -n> D := λne Δ, PersPred (λ w, ⌜w = #LitUnit⌝)%I.
  Definition interp_nat : listO D -n> D :=
    λne Δ, PersPred (λ w, ⌜∃ (n:Z), w = # n⌝)%I.
  Definition interp_boxednat : listO D -n> D :=
    λne Δ, PersPred (λ w, ⌜∃ (n:Z), w = # (LitBoxedInt n)⌝)%I.
  Definition interp_bool : listO D -n> D :=
    λne Δ, PersPred (λ w, ⌜∃ (b:bool), w = # b⌝)%I.

  Program Definition interp_prod
          (interp1 interp2 : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ w, ∃ w1 w2, ⌜w = (PairV w1 w2)⌝ ∧
                            interp1 Δ w1 ∧ interp2 Δ w2)%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Program Definition interp_sum
      (interp1 interp2 : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ w, (∃ w1, ⌜w = InjLV w1⌝ ∧ interp1 Δ w1) ∨
                   (∃ w2, ⌜w = InjRV w2⌝ ∧ interp2 Δ w2))%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Program Definition interp_arrow
      (interp1 interp2 : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ w, ∃ b1 b2 e, ⌜w = RecV b1 b2 e⌝ ∗ □ ∀ v, interp1 Δ v → na_tok -∗
                        WP App w v {{ λ o, (∃v, ⌜o = OVal v⌝ ∗ interp2 Δ v) ∗ na_tok }})%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Program Definition interp_forall
      (interp : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ w, □ ∀ τi : D,
      na_tok -∗ WP TApp w {{ λ o, (∃v, ⌜o = OVal v⌝ ∗ interp (τi :: Δ) v) ∗ na_tok }})%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Program Definition interp_exist (interp : listO D -n> D) : listO D -n> D :=
    λne Δ, PersPred (λ w, ∃ (τi : D) v, ⌜w = PackV v⌝ ∗ interp (τi :: Δ) v)%I.
  Solve Obligations with repeat intros ?; simpl; solve_proper.

  Definition interp_rec1 (interp : listO D -n> D) (Δ : listO D) (τi : D) : D :=
    PersPred (λ w, □ (∃ v, ⌜w = RollV v⌝ ∧ ▷ interp (τi :: Δ) v))%I.

  Global Instance interp_rec1_contractive
    (interp : listO D -n> D) (Δ : listO D) : Contractive (interp_rec1 interp Δ).
  Proof. by solve_contractive. Qed.

  Lemma fixpoint_interp_rec1_eq (interp : listO D -n> D) Δ x :
    fixpoint (interp_rec1 interp Δ) x ≡
    interp_rec1 interp Δ (fixpoint (interp_rec1 interp Δ)) x.
  Proof. exact: (fixpoint_unfold (interp_rec1 interp Δ) x). Qed.

  Program Definition interp_rec (interp : listO D -n> D) : listO D -n> D :=
    λne Δ, fixpoint (interp_rec1 interp Δ).
  Next Obligation.
    intros interp n Δ1 Δ2 HΔ; apply fixpoint_ne => τi w. solve_proper.
  Qed.

  Program Definition interp_array_inv_L γ (l : loc) : iPropO Σ :=
    (∃ vs, l ↦∗ vs ∗ ghost_var γ (1/2) vs)%I.
  Program Definition interp_array_inv_R γ : D -n> iPropO Σ := λne τiv,
    (∃ vs, ([∗ list] v∈vs, τiv v) ∗ ghost_var γ (1/2) vs)%I.
  Solve Obligations with solve_proper.

  Program Definition interp_array (interp : listO D -n> D) : listO D -n> D :=
    λne Δ,
    PersPred (λ w, ∃ γ (l:loc), ⌜w = # l⌝ ∧
                      na_inv logrel_nais (nroot .@ "timeless" .@ l) (interp_array_inv_L γ l) ∗
                      na_inv logrel_nais (nroot .@ "typing"   .@ l) (interp_array_inv_R γ (interp Δ)))%I.
  Solve Obligations with solve_proper.

  Fixpoint interp (τ : type) : listO D -n> D :=
    match τ return _ with
    | TUnit => interp_unit
    | TNat => interp_nat
    | TBoxedNat => interp_boxednat
    | TBool => interp_bool
    | TProd τ1 τ2 => interp_prod (interp τ1) (interp τ2)
    | TSum τ1 τ2 => interp_sum (interp τ1) (interp τ2)
    | TArrow τ1 τ2 => interp_arrow (interp τ1) (interp τ2)
    | TVar x => env_lookup x
    | TForall τ' => interp_forall (interp τ')
    | TExist τ' => interp_exist (interp τ')
    | TRec τ' => interp_rec (interp τ')
    | TArray τ' => interp_array (interp τ')
    end.
  Notation "⟦ τ ⟧" := (interp τ).

  Definition interp_env (Γ : gmap string type)
      (Δ : listO D) (vs : gmap string val) : iProp Σ :=
    ([∗ map] x↦τ;v ∈ Γ;vs, ⟦ τ ⟧ Δ v)%I.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Definition prog_env_proto (p_types : gmap string program_type) (Δ : listO D) : protocol val Σ :=
    (λ s vv Φ, ∃ tl tr, ⌜p_types !! s = Some (FunType tl tr)⌝
                      ∗ ([∗ list] k↦τ;v ∈ tl;vv, ⟦ τ ⟧ Δ v)
                      ∗ na_tok
                      ∗ (∀ vr, ⟦ tr ⟧ Δ vr -∗ na_tok -∗ Φ (OVal vr)))%I.

  (* Compare with language/wp_link.v
     The difference between this and program_fulfills is that we allow axiomatically specified
     functions to be well-typed.*)

  Definition interp_prog_env (p_types : gmap string program_type) (Δ : listO D) : iProp Σ :=
    (□ ∀ s vv Φ, prog_env_proto p_types Δ s vv Φ -∗ WP (of_call _ s vv) {{o, Φ o}}).

  Definition interp_expr (τ : type) (Δ : listO D) (e : expr ML_lang) : iProp Σ :=
    na_tok -∗ WP e {{ λ o, (∃v, ⌜o = OVal v⌝ ∗ ⟦ τ ⟧ Δ v) ∗ na_tok }}%I.

  Global Instance interp_env_base_persistent Δ Γ vs :
  TCForall Persistent (zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs).
  Proof. revert vs; induction Γ => vs; destruct vs; constructor; apply _. Qed.
  Global Instance interp_env_persistent Γ Δ vs : Persistent (⟦ Γ ⟧* Δ vs) := _.

  Lemma interp_weaken Δ1 Π Δ2 τ :
    ⟦ τ.[upn (length Δ1) (ren (+ length Π))] ⟧ (Δ1 ++ Π ++ Δ2)
    ≡ ⟦ τ ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Π Δ2. induction τ=> Δ1 Π Δ2; simpl; auto; intros ?; simpl.
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - f_equiv.
      apply fixpoint_proper=> τi w /=.
      by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      rewrite !lookup_app_r; [|lia ..]; do 3 f_equiv; lia.
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
  Qed.

  Lemma interp_subst_up Δ1 Δ2 τ τ' :
    ⟦ τ ⟧ (Δ1 ++ interp τ' Δ2 :: Δ2)
    ≡ ⟦ τ.[upn (length Δ1) (τ' .: ids)] ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Δ2; induction τ=> Δ1 Δ2; simpl; auto; intros ?; simpl.
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
    - f_equiv.
      apply fixpoint_proper=> τi w /=.
      by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - match goal with |- context [_ !! ?x] => rename x into idx end.
      rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      rewrite !lookup_app_r; [|lia ..].
      case EQ: (idx - length Δ1) => [|n]; simpl.
      { symmetry. asimpl. apply (interp_weaken [] Δ1 Δ2 τ'). }
      rewrite !lookup_app_r; [|lia ..]. do 3 f_equiv. lia.
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply (IH (_ :: _)) end).
    - by repeat (f_equiv; try match goal with IH : ∀ _, _ |- _ => by apply IH end).
  Qed.

  Lemma interp_subst Δ2 τ τ' v : ⟦ τ ⟧ (⟦ τ' ⟧ Δ2 :: Δ2) v ≡ ⟦ τ.[τ'/] ⟧ Δ2 v.
  Proof. apply (interp_subst_up []). Qed.

  Lemma interp_env_dom Δ Γ vs : ⟦ Γ ⟧* Δ vs ⊢ ⌜dom Γ = dom vs⌝.
  Proof. iIntros "H". by iApply big_sepM2_dom. Qed.

  Lemma interp_env_Some_l Δ Γ vs x τ :
    Γ !! x = Some τ → ⟦ Γ ⟧* Δ vs ⊢ ∃ v, ⌜vs !! x = Some v⌝ ∧ ⟦ τ ⟧ Δ v.
  Proof.
    iIntros (?) "HΓ". iAssert (⌜x ∈ dom vs⌝)%I as "%HH".
    1: { iPoseProof (interp_env_dom with "HΓ") as "<-". iPureIntro. by eapply elem_of_dom_2. }
    revert HH; intros [v Hv]%elem_of_dom.
    iExists v; iSplitR; first done.
    iPoseProof (big_sepM2_lookup with "HΓ") as "HΓ". 1-2: done. done.
  Qed.

  Lemma interp_env_nil Δ : ⊢ ⟦ ∅ ⟧* Δ ∅.
  Proof. iApply big_sepM2_empty. done. Qed.
  Lemma interp_env_insert Δ Γ vs τ v x :
    Γ !! x = None → vs !! x = None →
    (⟦ <[x:=τ]> Γ ⟧* Δ ( <[x:=v]> vs) ⊣⊢ ⟦ τ ⟧ Δ v ∗ ⟦ Γ ⟧* Δ vs).
  Proof.
    intros H1 H2. by iApply big_sepM2_insert.
  Qed.

  Lemma interp_env_insert_2 Δ Γ vs τ v x :
    ⟦ τ ⟧ Δ v -∗ ⟦ Γ ⟧* Δ vs -∗ ⟦ <[x:=τ]> Γ ⟧* Δ ( <[x:=v]> vs).
  Proof. iApply big_sepM2_insert_2. Qed.

  Lemma interp_env_binder_insert_2 Δ Γ vs τ v x :
    ⟦ τ ⟧ Δ v -∗ ⟦ Γ ⟧* Δ vs -∗ ⟦ binder_insert x τ Γ ⟧* Δ ( binder_insert x v vs).
  Proof. destruct x; try iApply big_sepM2_insert_2. iIntros "_ $". Qed.

  Lemma interp_env_ren Δ (Γ : gmap string type) (vs : gmap string val) τi :
    ⟦ subst (ren (+1)) <$> Γ ⟧* (τi :: Δ) vs ⊣⊢ ⟦ Γ ⟧* Δ vs.
  Proof.
    iStartProof.
    iSplit; iIntros "H";
    iPoseProof (interp_env_dom with "H") as "%Hdom".
    all: try rewrite dom_fmap_L in Hdom.
    all: (iPoseProof big_sepM2_fmap_l as "[HL HR]").
    - iPoseProof ("HL" with "H") as "H". iClear "HL HR".
      iApply (big_sepM2_wand with "H"). iApply big_sepM2_intro.
      1: intros k; erewrite <- !elem_of_dom, Hdom; done.
      iIntros "!> %k %τ %v %H1 %H2 H". iPoseProof (interp_weaken [] [τi] Δ with "H") as "H". done.
    - iApply "HR"; iClear "HL HR".
      iApply (big_sepM2_wand with "H"). iApply big_sepM2_intro.
      1: intros k; erewrite <- !elem_of_dom, Hdom; done.
      iIntros "!> %k %τ %v %H1 %H2 H". iApply (interp_weaken [] [τi] Δ). done.
  Qed.

  Lemma interp_prog_env_ren Δ P τi :
    interp_prog_env (subst_prog_env (ren (+1)) P) (τi :: Δ) ⊣⊢ interp_prog_env P Δ.
  Proof.
    iStartProof. unfold interp_prog_env.
    iSplit; iIntros "#H !>" (s vv Φ); iIntros "(%tl&%tr&%Ht&Htl&Htok&HWP)"; iApply ("H"); iFrame "Htok".
    - rewrite /subst_prog_env lookup_fmap Ht; iExists _, _. iSplit; first done.
      iSplitL "Htl".
      { iApply big_sepL2_fmap_l.
        iPoseProof (big_sepL2_length with "Htl") as "%Hlen".
        iApply (big_sepL2_wand with "Htl").
        iApply big_sepL2_intro; first done.
        iIntros "!> %k %τ1 %v1 %H1 %H2 HH". iPoseProof (interp_weaken [] [τi] Δ with "HH") as "HHH". done. }
      { iIntros (vr) "Hvr Htok". iApply ("HWP" with "[Hvr] Htok").
        iPoseProof (interp_weaken [] [τi] Δ with "Hvr") as "HHH". done. }
    - rewrite /subst_prog_env in Ht. apply lookup_fmap_Some in Ht as ([tl' tr']&Hlu&HH). rewrite HH.
      iExists _, _. iSplit; first done.
      cbn in Hlu. simplify_eq.
      iSplitL "Htl".
      { iPoseProof (big_sepL2_length with "Htl") as "%Hlen".
        iDestruct big_sepL2_fmap_l as "[HHL HHR]"; iPoseProof ("HHL" with "Htl") as "Hl'".
        iApply (big_sepL2_wand with "Hl'").
        rewrite fmap_length in Hlen.
        iApply big_sepL2_intro; first done.
        iIntros "!> %k %τ1 %v1 %H1 %H2 HH". iPoseProof (interp_weaken [] [τi] Δ with "HH") as "HHH". done. }
      { iIntros (vr) "Hvr Htok". iApply ("HWP" with "[Hvr] Htok").
        iPoseProof (interp_weaken [] [τi] Δ with "Hvr") as "HHH". done. }
  Qed.
End logrel.

Global Typeclasses Opaque interp_env.

Global Instance interp_array_inv_L_timeless `{SI: indexT} `{!heapG_ML Σ, !logrelG Σ} γ l : Timeless (interp_array_inv_L γ l).
Proof. apply _. Qed.

Notation "⟦ P ⟧ₚ*  x" := (interp_prog_env x P) (at level 10).
Notation "⟦ τ ⟧  x" := (interp x τ) (at level 10).
Notation "⟦ τ ⟧ₑ  x" := (interp_expr x τ) (at level 10).
Notation "⟦ Γ ⟧*  x" := (interp_env x Γ) (at level 10).

