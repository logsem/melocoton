From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props multirelations.
From melocoton.ml_lang.logrel Require Import typing logrel fundamental.
From melocoton.language Require Import language weakestpre.
From melocoton.interop Require Import basics basics_resources prims_proto.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import state lang weakestpre update_laws wp_utils wp_simulation.
From melocoton.ml_lang Require Import primitive_laws lang_instantiation.
From melocoton.c_lang Require Import lang_instantiation mlang_instantiation.
From melocoton.mlanguage Require Import progenv.
From melocoton.mlanguage Require Import weakestpre mlanguage adequacy.
From melocoton.linking Require Import lang weakestpre.
From transfinite.base_logic.lib Require Import satisfiable invariants ghost_map ghost_var na_invariants.
From transfinite.stepindex Require Import ordinals.
From melocoton.combined Require Import rules.

Notation combined_lang := (link_lang wrap_lang C_mlang).
Notation combined_prog e p := (link_prog wrap_lang C_mlang (wrap_prog e) p).


Class ffiGpre `{SI: indexT} (Σ : gFunctors) : Set := FFIGpre {
  ffiGpre_CG :> heapGpre_C Σ;
  ffiGpre_MLG :> heapGpre_ML Σ;
  ffiGpre_wrapperBasicsG :> wrapperBasicsGpre Σ;
  ffiGpre_wrapperGCtokG :> wrapperGCtokGpre Σ;
  ffiGpre_linkG :> linkGpre Σ;
  ffiGpre_logrelG :> logrelGpre Σ;
}.

Definition ffiΣ {SI: indexT} : gFunctors :=
  #[invΣ; heapΣ_C; heapΣ_ML; wrapperΣ; linkΣ; logrelΣ].

Global Instance subG_ffiGpre `{SI: indexT} Σ :
  subG ffiΣ Σ → ffiGpre Σ.
Proof. solve_inG. Qed.

Global Instance subG_ffiΣ_invPreG `{SI: indexT} Σ :
  subG ffiΣ Σ → invPreG Σ.
Proof. solve_inG. Qed.

Global Instance subG_ffiΣ_logrelGpre `{SI: indexT} Σ :
  subG ffiΣ Σ → logrelGpre Σ.
Proof. solve_inG. Qed.

Definition na_tok_of {SI: indexT} `{!logrelG Σ} := na_tok.

Section AllocBasics.
  Existing Instance ordI.
  Context `{Σ : gFunctors}.
  Context `{!invG Σ}. (* we already have invariants *)

  Lemma alloc_heapG_ML `{!heapGpre_ML Σ} : @Alloc _ Σ (heapG_ML Σ) 
      (λ _, state_interp (∅ : language.state ML_lang) (* ∗ ml_lang.primitive_laws.inv_heap_inv *) )%I True.
  Proof using.
    intros P _ Halloc.
    eapply alloc_fresh_res in Halloc as (γheap&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γmeta&Halloc).
    - pose (GenHeapG _ ((list MLval)) _ γheap γmeta) as Hgen_heapG.
      pose (HeapG_ML _ _ Hgen_heapG) as HheapG_ML.
      exists HheapG_ML. eapply alloc_mono; last exact Halloc.
      iIntros "(($&H1)&H2)".
      iExists ∅. iSplit; first done. cbn in *. iFrame.
    - eapply gmap_view.gmap_view_auth_valid.
    - eapply gmap_view.gmap_view_auth_valid.
  Qed.

  Lemma alloc_heapG_C `{!heapGpre_C Σ}  : @Alloc _ Σ (heapG_C Σ) 
      (λ _, state_interp (∅ : language.state C_lang) (* ∗ ml_lang.primitive_laws.inv_heap_inv *) )%I True.
  Proof.
    intros P _ Halloc.
    eapply alloc_fresh_res in Halloc as (γheap&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γmeta&Halloc).
    - pose (GenHeapG _ heap_cell _ γheap γmeta) as Hgen_heapG.
      pose (HeapG _ _ Hgen_heapG) as HheapG_ML.
      exists HheapG_ML. eapply alloc_mono; last exact Halloc.
      iIntros "(($&H1)&H2)".
      iExists ∅. iSplit; first done. cbn in *. iFrame.
    - eapply gmap_view.gmap_view_auth_valid.
    - eapply gmap_view.gmap_view_auth_valid.
  Qed.

  Lemma alloc_wrapperBasicsG `{!wrapperBasicsGpre Σ} : @Alloc _ Σ (wrapperBasicsG Σ) 
      (λ _, lstore_own_auth ∅ ∗ lloc_own_auth ∅ ∗ ghost_map_auth wrapperG_γroots_map 1 (∅:gmap addr lval) ∗ ⌜basics_resources.wrapperG_inG = _⌝)%I True.
  Proof.
    intros P _ Halloc.
    eapply alloc_fresh_res in Halloc as (γζvirt&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γχvirt&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γroots_map&Halloc).
    - pose (WrapperBasicsG _ Σ _ γζvirt γχvirt γroots_map) as HWrapperBasicsG.
      exists HWrapperBasicsG. eapply alloc_mono; last exact Halloc.
      iIntros "((($&H1)&H2)&H3)". unfold lstore_own_auth, lloc_own_auth.
      rewrite /named /ghost_map_auth !ghost_map.ghost_map_auth_aux.(seal_eq) /ghost_map.ghost_map_auth_def.
      cbn in *. iFrame. repeat iSplitL.
      + unfold lstore_immut_blocks. rewrite map_filter_empty. by iApply big_sepM_empty.
      + unfold lloc_map_pubs. rewrite omap_empty. by iApply big_sepM_empty.
      + unfold lloc_map_foreign. rewrite omap_empty. by iApply big_sepM_empty.
      + done.
    - eapply gmap_view.gmap_view_auth_valid.
    - eapply gmap_view.gmap_view_auth_valid.
    - eapply gmap_view.gmap_view_auth_valid.
  Qed.

Definition GCtok_gammas `{!wrapperGCtokG Σ} : iProp Σ :=
    "GCζ" ∷ ghost_var wrapperG_γζ 1 (∅:lstore)
  ∗ "GCχ" ∷ ghost_var wrapperG_γχ 1 (∅:lloc_map)
  ∗ "GCθ" ∷ ghost_var wrapperG_γθ 1 (∅:addr_map)
  ∗ "GCroots" ∷ ghost_var wrapperG_γroots_set 1 (∅:gset addr)
  ∗ "GCζvirt" ∷ lstore_own_auth (∅:lstore)
  ∗ "GCχvirt" ∷ lloc_own_auth (∅:lloc_map)
  ∗ "GCrootsm" ∷ ghost_map_auth wrapperG_γroots_map 1 (∅:gmap addr lval)
  ∗ "HInit" ∷ ghost_var wrapperG_γat_init 1 true.

  Context `{!ffiGpre Σ}.

  Lemma alloc_wrapperGCtokG : @Alloc _ Σ (wrapperGCtokG Σ) 
      (λ H, GCtok_gammas 
          ∗ ⌜wrapperG_inG = _⌝
          ∗ ⌜basics_resources.wrapperG_inG = _⌝)%I True.
  Proof using All.
    intros P _ Halloc.
    eapply alloc_wrapperBasicsG in Halloc as (HwrapperBasicG&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γζ&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γχ&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γθ&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γroots_set&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γat_init&Halloc).
    - pose (WrapperGCtokG _ Σ _ _ γζ γχ γθ γroots_set γat_init) as HWrapperGCtokG.
      exists HWrapperGCtokG. eapply alloc_mono; last exact Halloc.
      unfold GCtok_gammas; cbn.
      rewrite /ghost_var !ghost_var.ghost_var_aux.(seal_eq) /ghost_var.ghost_var_def; cbn.
      iIntros "(((((($&($&($&(H&->))))&$)&$)&$)&$)&$)". iFrame "H".
      done.
    - cbv; done.
    - cbv; done.
    - cbv; done.
    - cbv; done.
    - cbv; done.
    - cbv; done.
  Qed.

  Lemma alloc_wrapperG : @Alloc _ Σ (prod (wrapperG Σ) (heapG_ML Σ))
      (λ '(HW,HML), weakestpre.private_state_interp {| χC := ∅; ζC := ∅; θC := ∅; rootsC := ∅ |} 
               ∗ ghost_var wrapperG_γat_boundary (1 / 2) true ∗ at_init
               ∗ ⌜wrapperG_inG = _⌝)%I True.
  Proof using All.
    intros P _ Halloc.
    eapply alloc_heapG_ML in Halloc as (HheapG_ML&Halloc); last done.
    eapply alloc_wrapperGCtokG in Halloc as (HwrapperGCtokG&Halloc); last done.
    1: eapply alloc_fresh_res in Halloc as (γboundary&Halloc).
    - pose (WrapperG _ Σ HwrapperGCtokG γboundary) as HwrapperG.
      exists (HwrapperG,HheapG_ML). eapply alloc_mono; last exact Halloc. cbn.
      unfold weakestpre.private_state_interp, C_state_interp, at_init.
      iIntros "(((H1&H2)&(H3&(%Heq&%Heq2)))&H4)". iFrame "H1". iNamed "H3". cbn.
      iAssert (ghost_var γboundary (1 / 2) true ∗ ghost_var γboundary (1 / 2) true)%I with "[H4]" as "(H4&H4')".
      { rewrite /ghost_var !ghost_var.ghost_var_aux.(seal_eq) /ghost_var.ghost_var_def; cbn.
        iApply own_op. iApply "H4". }
      rewrite <- !Heq.
      iDestruct "HInit" as "(HInit1&HInit2)". iFrame. iSplitL; last done.
      iExists true. unfold preGCtok, named. cbn.
      iFrame.
      iDestruct "GCζ" as "($&$)".
      iDestruct "GCχ" as "($&$)".
      iDestruct "GCθ" as "($&$)".
      iDestruct "GCroots" as "($&$)".
    - eapply dfrac_agree.frac_agree_op_valid_L; done.
  Qed.

  Lemma alloc_linkG (s:link_state_case) : @Alloc _ Σ (linkG Σ)
      (λ _, ghost_var linkG_γ 1 s ∗ ⌜linkG_preG = _⌝)%I True.
  Proof using All.
    intros P _ Halloc.
    1: eapply alloc_fresh_res in Halloc as (γlink&Halloc).
    - pose (LinkG _ Σ _ γlink) as HLinkG.
      exists HLinkG. eapply alloc_mono; last exact Halloc. cbn.
      rewrite /ghost_var !ghost_var.ghost_var_aux.(seal_eq) /ghost_var.ghost_var_def; cbn.
      iIntros "($&$)". done.
    - cbv. done.
  Qed.

  Lemma alloc_logrelG  `{!logrelGpre Σ} : @Alloc _ Σ (logrel.logrelG Σ)
      (λ _, na_tok_of)%I True.
  Proof using.
    intros P _ Halloc.
    1: eapply alloc_fresh_res in Halloc as (γnais&Halloc).
    - pose (LogrelG _ Σ logrel_na_invG_pre wrapperG_addrmapG_pre γnais) as HLogrelG.
      exists HLogrelG. eapply alloc_mono; last exact Halloc. cbn.
      iIntros "($&H)". iApply "H".
    - cbv. done.
  Qed.


End AllocBasics.

Local Definition σ_init {SI:indexT} : state combined_lang :=
  @Link.St _ _ wrap_lang C_mlang _ _
    (∅:c_state) {| χC := ∅; ζC := ∅; θC := ∅; rootsC := ∅ |} ().
Section MainAlloc.
  Existing Instance ordI.
  Context `{Σ : gFunctors}.
  Context `{!invG Σ}. (* we already have invariants *)
  Context `{!ffiGpre Σ}.
  Notation CIntV x := (C_intf.LitV (C_intf.LitInt x)).
  Notation MLIntV x := (LitV (LitInt x)).

  Notation Φpure Φ := (λ _ w, ∃ x, w = code_int x ∧ Φ x).
  Notation Φbi Φ := (λ w, ∃ x, ⌜w = code_int x ∧ Φ x⌝)%I.
  Lemma alloc_main p Φ :
    (∀ `{!heapG_C Σ, !heapG_ML Σ, !wrapperG Σ, !linkG Σ, !logrelG Σ},
       ⊥ |- p :: main_proto Φ na_tok_of) →
    @Alloc _ Σ (mlangG word combined_lang Σ)
      (λ HH : mlangG word combined_lang Σ,
         (sideConds combined_lang (Φpure Φ) p ⊥ (Φbi Φ)) ∗
          state_interp σ_init ∗
          (WP (LkCall "main" []) at ⟪p,⊥⟫ {{ w, ∃ x : Z, ⌜w = code_int x ∧ Φ x⌝ }}))%I
      True.
  Proof using All.
    intros Hspec P _ Halloc.
    eapply (alloc_linkG Boundary) in Halloc as (HlinkG&Halloc); last done.
    eapply alloc_wrapperG in Halloc as ((HwrapperG&HheapG_ML)&Halloc); last done.
    eapply alloc_heapG_C in Halloc as (HheapG_C&Halloc); last done.
    eapply alloc_logrelG in Halloc as (HlogrelG&Halloc); last done.
    exists (link_mlangG wrap_lang C_mlang _).
    eapply alloc_mono; last exact Halloc.
    iIntros "(((($&(Hb1&Hb2)&%Heq1)&((%b&HσW)&Hbound&Hinit2&%Heq2))&HσC)&Htok)". iNamed "HσW". cbn.
    rewrite // /weakestpre.private_state_interp // /C_state_interp // -!Heq1 -!Heq2.
    iPoseProof (ghost_var_agree with "SIinit Hinit2") as "->".
    iFrame. iSplitR.
    2: iSplitL "Hb1 SIinit Hinit".
    2: { iSplitL "Hb1". 1: iExists _; iFrame; eauto. iExists true; iFrame. }
    { iSplit; iIntros "!>".
      - by iIntros (? ?) "[? %H] !>".
      - iIntros (? ? ?). done. }
    pose (FFIG _ _ _ _ _ _ _ _) as FFI.
    specialize (Hspec _ _ _ _ _).
    pose proof (Hspec "main" [] (λ w, ∃ x, ⌜w = code_int x ∧ Φ x⌝)%I) as Hspecm.
    iDestruct (Hspecm with "[Hinit2 Htok]") as "Hmain".
    { rewrite /main_proto /named. do 2 (iSplit; first done). iFrame.
      iIntros "!>" (? ?). eauto. }

    rewrite (_: LkCall "main" [] = to_call _ "main" []) //.
    iApply (@wp_internal_call_at_boundary with "[Hb2 SIbound] Hmain").
    { by iFrame. }
    iIntros "!>" (v) "[% ?]". eauto.
  Qed.

End MainAlloc.

Local Existing Instance ordI.

(* Adequacy statements for a closed program with a sound "main" function *)

Lemma main_adequacy_trace (p : mlang_prog combined_lang) Φ :
  (∀ `{!ffiG Σ}, ⊥ |- p :: main_proto Φ na_tok) →
  umrel.trace (prim_step p) (LkCall "main" [], σ_init)
    (λ '(e, σ), ∃ x, to_val e = Some (code_int x) ∧ Φ x).
Proof using All.
  intros Hspec. eapply umrel_upclosed.
  1: eapply (@alloc_adequacy_coind _ combined_lang ffiΣ (λ _ w, ∃ x, w = code_int x ∧ Φ x) p ⊥
               (λ w, ∃ (x:Z), ⌜w = code_int x ∧ Φ x⌝)%I).
  { apply _. }
  2: { intros [? ?] (? & ? & HH). naive_solver. }
  intros Hinv. eapply (alloc_main p). intros Hffi ? ? ? ?.
  by pose proof (Hspec ffiΣ (FFIG _ _ _ _ _ _ _ _)).
Qed.

Lemma main_adequacy_star (p : mlang_prog combined_lang) Φ X :
  (∀ `{!ffiG Σ}, ⊥ |- p :: main_proto Φ na_tok) →
  umrel.star_AD (prim_step p) (LkCall "main" [], σ_init) X →
  ∃ e σ, X (e, σ) ∧ (∀ x, to_val e = Some (code_int x) → Φ x).
Proof using All.
  intros Hspec HWP.
  unshelve epose proof (@alloc_adequacy _ combined_lang ffiΣ (λ _ w, ∃ x, w = code_int x ∧ Φ x) p ⊥
            (λ w, ∃ x, ⌜w = code_int x ∧ Φ x⌝)%I _ (LkCall "main" []) σ_init _ _ HWP)
    as HH.
  2: { destruct HH as (? & ? & ? & HH). eexists _, _. split; eauto.
       intros y Hy. destruct (HH (code_int y)) as (? & ?%code_int_inj & ?); eauto.
       by simplify_eq. }
  intros Hinv. eapply (alloc_main p). intros Hffi ? ? ? ?.
  by specialize (Hspec ffiΣ (FFIG _ _ _ _ _ _ _ _)); cbn in *.
Qed.


(* All-in-one adequacy statement starting from ML and C programs *)

Lemma combined_adequacy_trace
  (e : ML_lang.expr) (p : lang_prog C_lang)
  (Ψ : ∀ `{!ffiG Σ}, protocol ML_lang.val Σ)
  (Pret : Z → Prop)
:
  (∀ `{!ffiG Σ},
    Ψ on prim_names ⊑ ⊥ ∧
    dom p ## prim_names ∧
    (⊢ na_tok -∗ WP e at ⟨ ∅ , Ψ ⟩ {{ k, ⌜∃ x, k = (ML_lang.LitV (ML_lang.LitInt x)) ∧ Pret x⌝ }}) ∧
    prims_proto Ψ ||- p :: wrap_proto Ψ
  ) →
  umrel.trace (prim_step (combined_prog e p))
    (LkCall "main" [], σ_init)
    (λ '(e, σ), ∃ x, to_val e = Some (code_int x) ∧ Pret x).
Proof.
  intros Hspec. apply main_adequacy_trace. intros Σ Hffi.
  specialize (Hspec Σ Hffi) as (HΨ & Hdomp & He & Hp).
  by eapply combined_correct.
Qed.

Lemma typed_adequacy_trace
  (e : ML_lang.expr) (p : lang_prog C_lang)
  (Ψ : ∀ `{!ffiG Σ}, protocol ML_lang.val Σ)
  (Penv : program_env)
:
  (∀ `{!ffiG Σ},
    Ψ on prim_names ⊑ ⊥ ∧
    dom p ## prim_names ∧
    (⊢ log_typed (p := ⟨ ∅ , Ψ ⟩) Penv ∅ e TNat) ∧
    prog_env_proto ⟨ ∅ , Ψ ⟩ Penv nil ⊑ Ψ ∧
    prims_proto Ψ ||- p :: wrap_proto Ψ
  ) →
  umrel.trace (prim_step (combined_prog e p))
    (LkCall "main" [], σ_init)
    (λ '(e, σ), ∃ x, to_val e = Some (code_int x) ∧ True).
Proof.
  intros Hspec. eapply combined_adequacy_trace.
  intros Σ H; destruct (Hspec Σ H) as (HH1&HH2&HH3&HH4&HH5).
  split_and!. 1-2,4: done.
  iIntros "Htok".
  iPoseProof (HH3 $! nil ∅ with "[] [] Htok") as "Hsemtype".
  { iApply interp_env_nil. }
  { iIntros (s vv Φ) "!> H1". wp_extern. iModIntro; cbn. iApply HH4.
    unfold prog_env_proto.
    iDestruct "H1" as "(%tl&%tr&Heq&H1&H2&H3)". iExists tl,tr. iFrame.
    iIntros (vr) "Hvr Htok". wp_pures. iModIntro. iApply ("H3" with "Hvr Htok"). }
  { iApply (@language.weakestpre.wp_wand with "[Hsemtype]").
     - unfold env_subst. by rewrite ml_lang.metatheory.subst_all_empty.
     - cbn. iIntros (v) "((%n&->)&_)". iPureIntro. by eexists. }
Qed.

Lemma typed_adequacy_trace_simplified
  (e : ML_lang.expr) (p : lang_prog C_lang)
  (Ψ : ∀ `{!ffiG Σ}, protocol ML_lang.val Σ)
:
  (∀ `{!ffiG Σ},
    Ψ on prim_names ⊑ ⊥ ∧
    dom p ## prim_names ∧
    typed ∅ ∅ e TNat ∧
    prims_proto Ψ ||- p :: wrap_proto Ψ
  ) →
  umrel.trace (prim_step (combined_prog e p))
    (LkCall "main" [], σ_init)
    (λ '(e, σ), ∃ x, to_val e = Some (code_int x) ∧ True).
Proof.
  intros Hspec. eapply typed_adequacy_trace.
  intros Σ H; destruct (Hspec Σ H) as (HH1&HH2&HH3&HH5).
  split_and!; try done.
  { iApply fundamental. apply HH3. }
  iIntros (s vv Φ) "(%tl&%tr&%Heq&H1&H2&H3)".
  by rewrite lookup_empty in Heq.
Qed.