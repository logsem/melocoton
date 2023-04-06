From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props multirelations.
From melocoton.language Require Import language weakestpre.
From melocoton.interop Require Import basics basics_resources prims_proto.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import state lang weakestpre update_laws wp_utils wp_simulation.
From melocoton.ml_lang Require Import primitive_laws lang_instantiation.
From melocoton.c_lang Require Import lang_instantiation mlang_instantiation.
From melocoton.mlanguage Require Import progenv.
From melocoton.mlanguage Require Import weakestpre mlanguage adequacy.
From melocoton.linking Require Import lang weakestpre.
From transfinite.base_logic.lib Require Import satisfiable invariants ghost_map ghost_var.
From transfinite.stepindex Require Import ordinals.

Notation combined_lang := (link_lang wrap_lang C_mlang).
Notation combined_prog e p := (link_prog wrap_lang C_mlang (wrap_prog e) p).

Class ffiGpre `{SI: indexT} (Σ : gFunctors) : Set := FFIGpre {
  ffiGpre_CG :> heapGpre_C Σ;
  ffiGpre_MLG :> heapGpre_ML Σ;
  ffiGpre_wrapperBasicsG :> wrapperBasicsGpre Σ;
  ffiGpre_wrapperGCtokG :> wrapperGCtokGpre Σ;
  ffiGpre_linkG :> linkGpre Σ;
}.

Class ffiG `{SI: indexT} (Σ : gFunctors) : Set := FFIG {
  ffiG_invG :> invG Σ;
  ffiG_CG :> heapG_C Σ;
  ffiG_MLG :> heapG_ML Σ;
  ffiG_wrapperG :> wrapperG Σ;
  ffiG_linkG :> linkG Σ;
}.

Definition ffiΣ {SI: indexT} : gFunctors :=
  #[invΣ; heapΣ_C; heapΣ_ML; wrapperΣ; linkΣ].

Global Instance subG_ffiGpre `{SI: indexT} Σ :
  subG ffiΣ Σ → ffiGpre Σ.
Proof. solve_inG. Qed.

Global Instance subG_ffiΣ_invPreG `{SI: indexT} Σ :
  subG ffiΣ Σ → invPreG Σ.
Proof. solve_inG. Qed.

Section AllocBasics.
  Existing Instance ordI.
  Context `{Σ : gFunctors}.
  Context `{!invG Σ}. (* we already have invariants *)
  Context `{!ffiGpre Σ}.

  (* TODO do we need the invariant heap *)
  Lemma alloc_heapG_ML : @Alloc _ Σ (heapG_ML Σ) 
      (λ _, state_interp (∅ : language.state ML_lang) (* ∗ ml_lang.primitive_laws.inv_heap_inv *) )%I True.
  Proof using ffiGpre0.
    intros P _ Halloc.
    eapply alloc_fresh_res in Halloc as (γheap&Halloc).
    1: eapply alloc_fresh_res in Halloc as (γmeta&Halloc).
    - pose (GenHeapG _ (option (list MLval)) _ γheap γmeta) as Hgen_heapG.
      pose (HeapG_ML _ _ Hgen_heapG) as HheapG_ML.
      exists HheapG_ML. eapply alloc_mono; last exact Halloc.
      iIntros "(($&H1)&H2)".
      iExists ∅. iSplit; first done. cbn in *. iFrame.
    - eapply gmap_view.gmap_view_auth_valid.
    - eapply gmap_view.gmap_view_auth_valid.
  Qed.

  Lemma alloc_heapG_C : @Alloc _ Σ (heapG_C Σ) 
      (λ _, state_interp (∅ : language.state C_lang) (* ∗ ml_lang.primitive_laws.inv_heap_inv *) )%I True.
  Proof using ffiGpre0.
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

  Lemma alloc_wrapperBasicsG : @Alloc _ Σ (wrapperBasicsG Σ) 
      (λ _, lstore_own_auth ∅ ∗ lloc_own_auth ∅ ∗ ghost_map_auth wrapperG_γroots_map 1 (∅:gmap addr lval) ∗ ⌜basics_resources.wrapperG_inG = _⌝)%I True.
  Proof using ffiGpre0.
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
      iIntros "(((((($&($&($&($&$))))&$)&$)&$)&$)&$)". done.
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
      rewrite <- !Heq, <- ! Heq2.
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

  Notation Φpure Φ := (λ w _, ∃ x, w = code_int x ∧ Φ x).
  Notation Φbi Φ := (λ w, ∃ x, ⌜w = code_int x ∧ Φ x⌝)%I.

  Lemma alloc_main p Φ :
    (∀ `{!heapG_C Σ, !heapG_ML Σ, !wrapperG Σ, !linkG Σ},
       ⊥ |- p :: main_proto Φ) →
    @Alloc _ Σ (mlangG word combined_lang Σ)
      (λ HH : mlangG word combined_lang Σ,
         (sideConds combined_lang (Φpure Φ) p ⊥ (Φbi Φ)) ∗
          state_interp σ_init ∗
          (WP (LkCall "main" []) @ ⟪p,⊥⟫; ⊤ {{ w, ∃ x : Z, ⌜w = code_int x ∧ Φ x⌝ }}))%I
      True.
  Proof using All.
    intros Hspec P _ Halloc.
    eapply (alloc_linkG Boundary) in Halloc as (HlinkG&Halloc); last done.
    eapply alloc_wrapperG in Halloc as ((HwrapperG&HheapG_ML)&Halloc); last done.
    eapply alloc_heapG_C in Halloc as (HheapG_C&Halloc); last done.
    exists (link_mlangG wrap_lang C_mlang _).
    eapply alloc_mono; last exact Halloc.
    iIntros "((($&(Hb1&Hb2)&%Heq1)&((%b&HσW)&Hbound&Hinit2&%Heq2))&HσC)". iNamed "HσW". cbn.
    rewrite // /weakestpre.private_state_interp // /C_state_interp // -!Heq1 -!Heq2.
    iPoseProof (ghost_var_agree with "SIinit Hinit2") as "->".
    iFrame. iSplitR. 2: iSplitL "SIinit Hinit".
    2: { iExists true. iFrame. }
    { iSplit; iIntros "!>".
      - by iIntros (? ?) "[? %H] !>".
      - iIntros (? ? ?). done. }
    pose (FFIG _ _ _ _ _ _ _) as FFI.
    specialize (Hspec _ _ _ _ "main" [] (λ w, ∃ x, ⌜w = code_int x ∧ Φ x⌝)%I).
    iDestruct (Hspec with "[Hinit2]") as "Hmain".
    { rewrite /main_proto /named. do 2 (iSplit; first done). iFrame.
      iIntros "!>" (? ?). eauto. }
    iApply (@wp_internal_call_at_boundary with "[Hb1 SIbound] Hmain");
      [done|by iFrame|].
    iIntros "!>" (? (? & -> & ?)) "?".
    iApply @wp_value; first done. eauto.
  Qed.

End MainAlloc.

Local Existing Instance ordI.

(* Adequacy statements for a closed program with a sound "main" function *)

Lemma main_adequacy_trace (p : mlang_prog combined_lang) Φ :
  (∀ `{!ffiG Σ}, ⊥ |- p :: main_proto Φ) →
  umrel.trace (prim_step p) (LkCall "main" [], σ_init)
    (λ '(e, σ), ∃ x, to_val e = Some (code_int x) ∧ Φ x).
Proof using All.
  intros Hspec. eapply umrel_upclosed.
  1: eapply (@alloc_adequacy_coind _ combined_lang ffiΣ (λ w _, ∃ x, w = code_int x ∧ Φ x) p ⊥
               (λ w, ∃ (x:Z), ⌜w = code_int x ∧ Φ x⌝)%I).
  { apply _. }
  2: { intros [? ?] (? & ? & HH). naive_solver. }
  intros Hinv. eapply (alloc_main p). intros Hffi ? ? ?.
  by specialize (Hspec ffiΣ (FFIG _ _ _ _ _ _ _)).
Qed.

Lemma main_adequacy_star (p : mlang_prog combined_lang) Φ X :
  (∀ `{!ffiG Σ}, ⊥ |- p :: main_proto Φ) →
  umrel.star_AD (prim_step p) (LkCall "main" [], σ_init) X →
  ∃ e σ, X (e, σ) ∧ (∀ x, to_val e = Some (code_int x) → Φ x).
Proof using All.
  intros Hspec HWP.
  unshelve epose proof (@alloc_adequacy _ combined_lang ffiΣ (λ w _, ∃ x, w = code_int x ∧ Φ x) p ⊥
            (λ w, ∃ x, ⌜w = code_int x ∧ Φ x⌝)%I _ (LkCall "main" []) σ_init _ _ HWP)
    as HH.
  2: { destruct HH as (? & ? & ? & HH). eexists _, _. split; eauto.
       intros y Hy. destruct (HH (code_int y)) as (? & ?%code_int_inj & ?); eauto.
       by simplify_eq. }
  intros Hinv. eapply (alloc_main p). intros Hffi ? ? ?.
  by specialize (Hspec ffiΣ (FFIG _ _ _ _ _ _ _)).
Qed.


(* All-in-one adequacy statement starting from ML and C programs *)

Lemma combined_adequacy_trace
  (e : ML_lang.expr) (p : lang_prog C_lang)
  (Ψ : ∀ `{!ffiG Σ} (E: coPset), protocol ML_lang.val Σ)
  (Pret : Z → Prop)
:
  (∀ `{!ffiG Σ} E,
    Ψ E on prim_names ⊑ ⊥ ∧
    dom p ## prim_names ∧
    {{{ True }}} e @ ⟨∅, Ψ E⟩; E {{{ x, RET (ML_lang.LitV (ML_lang.LitInt x)); ⌜Pret x⌝ }}} ∧
    prims_proto E (Ψ E) ||- p @ E :: wrap_proto (Ψ E)
  ) →
  umrel.trace (prim_step (combined_prog e p))
    (LkCall "main" [], σ_init)
    (λ '(e, σ), ∃ x, to_val e = Some (code_int x) ∧ Pret x).
Proof.
  intros Hspec. apply main_adequacy_trace. intros Σ Hffi.
  specialize (Hspec Σ Hffi ⊤) as (HΨ & Hdomp & He & Hp).
  eapply prog_triple_mono_r; swap 1 2.
  { eapply link_close_correct.
    { rewrite dom_prims_prog. set_solver. }
    3: { apply wrap_correct; first done. apply He. }
    3: { apply lang_to_mlang_correct, Hp. }
    1: done.
    apply proto_refines_join_l. }
  { rewrite -proto_refines_join_l -proto_refines_join_r //. }
Qed.

(*
Section Alloc.
  Existing Instance ordI.
  Context `{Σ : gFunctors}.
  Context `{!invG Σ}. (* we already have invariants *)
  Context `{!ffiGpre Σ}.

  Context {Φpure : word → state combined_lang → Prop}.
  Context {p : mlang_prog combined_lang}.
  Context {Ψ : protocol word Σ}.
  Context {Φbi : word → iProp Σ}.

  Context (HΦ : ∀ `{!heapG_C Σ, !heapG_ML Σ, !wrapperG Σ, !linkG Σ},
            ⊢ ∀ (σ:state combined_lang) v, state_interp σ ∗ Φbi v ==∗ ⌜Φpure v σ⌝).
  Context (Hpeclosed : ∀ `{!heapG_C Σ, !heapG_ML Σ, !wrapperG Σ, !linkG Σ},
            ⊢ ∀ f s vv, penv_proto ⟪p,Ψ⟫ f s vv -∗ False).
  Context (e : expr combined_lang).
  Context (HWP : ∀ `{!heapG_C Σ, !heapG_ML Σ, !wrapperG Σ, !linkG Σ},
            ⊢ at_init -∗ link_in_state wrap_lang C_mlang In2 -∗ WP e @ ⟪p,Ψ⟫ ; ⊤ {{Φbi}}).

  Local Definition σ0 {SI:indexT} : state combined_lang :=
    @Link.St2 _ _ wrap_lang C_mlang _ _
      {| χC := ∅; ζC := ∅; θC := ∅; rootsC := ∅ |} (∅:c_state).

  Lemma allocate_linked_ml_c : @Alloc _ Σ (mlangG _ combined_lang Σ)
    (λ H, @sideConds _ combined_lang Σ Φpure p Ψ Φbi _ _
        ∗ state_interp σ0 ∗ WP e @ ⟪p,Ψ⟫ ; ⊤ {{Φbi}})%I True.
  Proof using All.
    intros P _ Halloc.
    eapply (alloc_linkG In2) in Halloc as (HlinkG&Halloc); last done.
    eapply alloc_wrapperG in Halloc as ((HwrapperG&HheapG_ML)&Halloc); last done.
    eapply alloc_heapG_C in Halloc as (HheapG_C&Halloc); last done.
    exists (link_mlangG wrap_lang C_mlang _).
    eapply alloc_mono; last exact Halloc.
    iIntros "((($&(Hb1&Hb2)&%Heq1)&((%b&HσW)&Hbound&Hinit2&%Heq2))&HσC)". iNamed "HσW". cbn.
    rewrite // /weakestpre.private_state_interp // /C_state_interp // -!Heq1 -!Heq2.
    iPoseProof (ghost_var_agree with "SIinit Hinit2") as "->".
    iFrame. iSplitR. 1: iSplitL. 3: iSplitL "SIinit Hinit".
    - iIntros "!>". iApply HΦ.
    - iIntros "!>". iApply Hpeclosed.
    - iExists true. iFrame.
    - iApply (HWP with "Hinit2 [$]").
  Qed.
End Alloc.

Section Simplified.

  Existing Instance ordI.
  Context {Σ : gFunctors}.

  Notation C_proto := (protocol C_intf.val Σ).
  Notation ML_proto := (protocol ML_lang.val Σ).

  Context (eML : language.expr ML_lang).
  Context (eC  : language.expr C_lang).
  Context (peC : lang_prog C_lang).
  Context (ΨML : ML_proto).
  Context (Φ   : word → Prop).

  (* XXX make masks less weird so that the ∅ here can be a ⊤ *)
  Context (Hspec : ∀ `{!ffiG Σ}, (prims_proto ∅ ΨML ||- peC @ ∅ :: wrap_proto ΨML)).
  (* One of them seems like it would be unnecessary, but I could not figure out which *)
  Context (HNoInternal : ∀ `{!ffiG Σ}, ΨML on (dom (prims_prog eML)) ⊑ ⊥).
  Context (HpeC : ∀ s, is_prim_name s → peC !! s = None).

  Local Instance LinkInstance `{!ffiG Σ} E : can_link
    wrap_lang C_mlang E
    (wrap_prog eML) (wrap_proto ΨML)
    peC (prims_proto ∅ eML ΨML)
  ⊥.
  Proof using All. econstructor.
    - eapply elem_of_disjoint. intros s H1%in_dom_prims_prog [x Hx]%elem_of_dom.
      epose proof (HpeC _ H1) as HH. by rewrite HH in Hx.
    - rewrite proto_on_refines. eapply prog_triple_mono_mask.
      2: by eapply lang_to_mlang_correct. solve_ndisj.
    - rewrite proto_on_refines.
      eapply (prog_triple_mono_mask ∅ _); first solve_ndisj.
      eapply wrap_correct. by eapply HNoInternal.
    - iIntros (? ? ?) "H". rewrite /proto_except.
      iDestruct "H" as (HH1%not_elem_of_dom) "H".
      iPoseProof (Hspec _ with "H") as (? HH2 ? ?) "HH"; simplify_eq.
      apply elem_of_dom_2 in HH2. apply not_elem_of_dom_2 in HH1. done.
    - eapply prims_proto_except_dom.
  Qed.

  Local Definition peL := link_prog wrap_lang C_mlang (wrap_prog eML) peC.
  Notation step := (prim_step peL).

  Context `{!invPreG Σ}.
  Context `{!ffiGpre Σ}.

  Lemma linking_adequacy X :
      (∀ `{!ffiG Σ}, at_init -∗ WP eC @ ⟨ peC , (prims_proto ∅ eML ΨML) ⟩ ; ⊤ {{v, ⌜Φ v⌝}} ) →
      (umrel.star_AD step (LkSE (Link.Expr2 eC), σ) X) →
      (∃ e σ, X (e, σ) ∧ (∀ v, to_val e = Some v → Φ v)).
  Proof using All.
    intros HWP.
    eapply (@alloc_adequacy _ Λ Σ (λ v _, Φ v) ⟪ peL , ⊥ ⟫ (λ v, ⌜Φ v⌝)%I _ _ σ).
    intros Hinv.
    eapply allocate_linked_ml_c.
    - by iIntros (H1 H2 H3 H4 σ v) "(_&$)".
    - iIntros (H1 H2 H3 H4 f s vv) "[]".
    - iIntros (H1 H2 H3 H4) "Hinit Hstate".
      pose (FFIG _ _ _ _ _ _ _) as HTG.
      iApply (@wp_wand with "[Hstate Hinit]").
      1: iApply (@wp_link_run2 _ Σ _ _ wrap_lang C_mlang _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eC _ (@LinkInstance HTG _) with "Hstate").
      2: { cbn. iIntros (v) "(H&_)". iApply "H". }
      iApply wp_lang_to_mlang.
      iApply (@language.weakestpre.wp_wand with "[Hinit]").
      1: iApply (HWP HTG with "Hinit").
      iIntros (v) "$".
  Qed.

End Simplified.

Definition σ_initial := σ.
*)
