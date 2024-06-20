From transfinite.base_logic.lib Require Import na_invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.combined Require Import rules adequacy.
From melocoton.linking Require Import lang weakestpre.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import basics basics_resources.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils prims_proto.
From melocoton.language Require Import weakestpre progenv.
From melocoton.c_interface Require Import notation defs resources.
From melocoton.c_interop Require Import rules notation.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.ml_lang.logrel Require fundamental logrel typing.
From melocoton.c_lang Require Import notation proofmode derived_laws.
From iris.algebra Require Import list gmap big_op.
From transfinite.base_logic.lib Require Import na_invariants ghost_var.


Definition box_create_code (v : C_lang.expr) : C_lang.expr :=
  let: "k" := malloc (#2) in
  "k" <- #LitNull ;;
  ("k" +ₗ #1) <- v ;;
  call: &"registerroot" with ("k" +ₗ #1) ;;
  let: "bk" := caml_alloc_custom ( ) in
  (Custom_contents ( "bk" ) := "k") ;;
  "bk".

Definition box_update_code (v' b : C_lang.expr) : C_lang.expr :=
  let: "k" := Custom_contents (b) in
  let: "ov" := *("k" +ₗ #1) in
  ("k" +ₗ #1) <- v' ;;
 (if: *"k" ≠ #LitNull
    then call: &"callback" with ( *"k", "ov")
    else Skip) ;;
  Val_int (#0) .

Definition box_listen_code (l b : C_lang.expr) : C_lang.expr :=
  let: "k" := Custom_contents (b) in
 (if: *"k" ≠ #LitNull
    then "k" <- l
    else "k" <- l ;; call: &"registerroot" with ("k")) ;;
  Val_int (#0) .

Definition box_prog : lang_prog C_lang :=
  {[ "box_create" := Fun [BNamed "v"] (box_create_code "v");
     "box_update" := Fun [BNamed "v'"; BNamed "b"] (box_update_code "v'" "b");
     "box_listen" := Fun [BNamed "l"; BNamed "b"] (box_listen_code "l" "b") ]}.

Section Proofs.
  Import melocoton.ml_lang.notation.
  Import fundamental logrel typing.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ, !logrelG Σ}.


  Notation D := (persistent_predO val (iPropI Σ)).
  Implicit Types τi : D.
  Implicit Types Δ : listO D.
  Implicit Types interp : listO D -n> D.

  Program Definition box_invariant_1 ℓ : D -n> iProp Σ := (λne (interp:D), ∃ lv v, ℓ ↦roots lv ∗ lv ~~ v ∗ interp v)%I.
  Solve Obligations with solve_proper.
  Program Definition box_invariant_2 ℓ : D -n> iProp Σ := λne (interp:D), ((∃ lv v, ℓ ↦roots lv ∗ lv ~~ v ∗ interp v) ∨
                                                                           (ℓ ↦C (#C LitNull)))%I.
  Solve Obligations with solve_proper.

  Program Definition box_interp : (protocol ML_lang.val Σ) -n> (listO D -n> D) -d> listO D -n> D := λne Ψ, λ interp, λne Δ, PersPred (
    λ v, ∃ (γ:nat) (ℓ:loc), ⌜v = #(LitForeign γ)⌝ ∗ γ ↦foreign[Immut] (#C ℓ) ∗
           na_inv logrel_nais (nroot .@ "value"   .@ γ) (box_invariant_1 (ℓ +ₗ 1) (interp Δ)) ∗
           na_inv logrel_nais (nroot .@ "callback".@ γ) (box_invariant_2 ℓ (interp_arrow ⟨ ∅ , Ψ ⟩ interp interp_unit Δ)))%I.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    solve_proper_prepare.
    do 27 first [intros ? | f_equiv].
    by apply wp_ne_proto.
  Qed.

  Section InPsi.
  Context (Ψ : protocol ML_lang.val Σ).

  Import melocoton.ml_lang.notation.

  Definition box_create_spec_ML : protocol ML_lang.val Σ :=
    !! interp Δ v
    {{ "#Hv" ∷ interp Δ v ∗ "Hna" ∷ na_tok }}
      "box_create" with [v]
    {{ vr, RETV vr; na_tok ∗ box_interp Ψ interp Δ vr }}.

  Definition box_update_spec_ML : protocol ML_lang.val Σ :=
    !! interp Δ vn vb
    {{
       "#Hvn" ∷ interp Δ vn ∗
       "Hna" ∷ na_tok ∗
       "#Hbox" ∷ ▷ box_interp Ψ interp Δ vb
    }}
      "box_update" with [vn; vb]
    {{ RETV #(); na_tok }}.

  Definition box_listen_spec_ML : protocol ML_lang.val Σ :=
    !! interp Δ vl vb
    {{
       "#Hvl" ∷ ▷ interp_arrow ⟨ ∅ , Ψ ⟩ interp interp_unit Δ vl ∗
       "#Hbox" ∷ ▷ box_interp Ψ interp Δ vb ∗
       "Hna" ∷ na_tok
    }}
      "box_listen" with [vl; vb]
    {{ RETV #(); na_tok }}.

  Import melocoton.c_lang.primitive_laws melocoton.c_lang.proofmode.

  Lemma box_create_correct :
    prims_proto Ψ ||- box_prog :: wrap_proto box_create_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamedProto "Hproto".
    iSplit; first done.
    destruct lvs as [|lvl [|??]]; try done.
    all: iEval (cbn) in "Hsim"; iDestruct "Hsim" as "(Hsimv&Hsim)"; try done.
    destruct ws as [|wv [|??]]; decompose_Forall.
    iIntros (Φ'') "Cont2".
    wp_pure _.
    wp_apply (wp_Malloc); [done..|].
    change (Z.to_nat 2) with 2. cbn.
    iIntros (ℓ) "(Hℓ0&Hℓ1&_)".
    replace ((ℓ +ₗ 0%nat)) with ℓ by by rewrite loc_add_0.
    wp_pures.
    wp_apply (wp_store with "Hℓ0"). iIntros "Hℓ0".
    wp_pures.
    wp_apply (wp_store with "Hℓ1"). iIntros "Hℓ1".
    wp_pures.
    wp_apply (wp_registerroot with "[$HGC $Hℓ1]"); [done..|].
    iIntros "(HGC&Hℓ1)". wp_pures.
    wp_apply (wp_alloc_foreign with "HGC"); [done..|].
    iIntros (θ1 γ w) "(HGC&Hγfgn&%Hrepr)".
    wp_pures.
    wp_apply (wp_write_foreign with "[$HGC $Hγfgn]"); [done..|].
    iIntros "(HGC&Hγfgn)". wp_pures.
    iDestruct "Hγfgn" as "(Hγfgn'&Hγfresh)".
    iMod (na_inv_alloc logrel_nais _ _ (box_invariant_1 (ℓ +ₗ 1) (interp Δ)) with "[Hℓ1]") as "#Hinv1".
    { iNext. iExists _, _. iFrame "Hℓ1 Hsimv Hv". }
    iMod (na_inv_alloc logrel_nais _ _ (box_invariant_2 ℓ (interp_arrow ⟨ ∅ , Ψ ⟩ interp interp_unit Δ)) with "[Hℓ0]") as "#Hinv2".
    { iNext. iRight. iFrame. }
    iMod (freeze_foreign_to_immut γ θ1 _ with "[$]") as "(HGC&#Hγfgn)".
    iModIntro. iApply "Cont2". iApply ("Return" $! θ1 (#(LitForeign γ)) with "HGC [-] [] []").
    2,3: done.
    iApply "Cont". iFrame "Hna". iExists γ, ℓ.
    iSplit; first done. 
    iSplitL; first done.
    iFrame "Hinv1 Hinv2".
  Qed.

  Lemma box_update_correct :
    prims_proto Ψ ||- box_prog :: wrap_proto box_update_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamedProto "Hproto".
    iSplit; first done.
    destruct lvs as [|lvn [|lvb [|??]]]; try done.
    all: iEval (cbn) in "Hsim"; iDestruct "Hsim" as "(Hsimvn&Hsim)"; try done.
    all: iEval (cbn) in "Hsim"; iDestruct "Hsim" as "(Hsimvb&Hsim)"; try done.
    destruct ws as [|wn [|wb [|??]]]; decompose_Forall.
    iIntros (Φ'') "Cont2".
    wp_pure _.
    iDestruct "Hbox" as (γ ℓ) "(->&#Hγfgn&#Hinv1&#Hinv2)".
    iDestruct "Hsimvb" as "->".
    iMod (na_inv_acc_open with "Hinv1 Hna") as "HH". 1-2: solve_ndisj.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgn]"); [done..|].
    iIntros "(HGC&_)". iDestruct "HH" as "((%lv1&%v1&Hℓ1&#Hlv1&#Hv1)&Hna&Hclose1)".
    iMod (na_inv_acc_open with "Hinv2 Hna") as "HH". 1-2: solve_ndisj.
    wp_pures. iDestruct "HH" as "(HI2&Hna&Hclose2)".
    wp_apply (load_from_root with "[$HGC $Hℓ1]").
    iIntros (wv1) "(Hℓ1&HGC&%Hwv1)". wp_pures.
    wp_apply (store_to_root with "[$HGC $Hℓ1]"); first done.
    iIntros "(HGC&Hℓ1)". wp_pures.

    iDestruct "HI2" as "[(%lv2&%v2&Hℓ0&#Hlv2&#(%b1&%b2&%ec&->&#Hcall))|Hℓ0]".
    - iDestruct "Hlv2" as (γcb ->) "Hlv2".
      wp_apply (load_from_root with "[$HGC $Hℓ0]").
      iIntros (wcb) "(Hℓ0&HGC&%Hwcb)". inversion Hwcb; simplify_eq.
      wp_pure _. 1: by destruct a.
      wp_pures.
      wp_apply (load_from_root with "[$HGC $Hℓ0]").
      iIntros (wcb) "(Hℓ0&HGC&%Hwcb')".
      iMod ("Hclose2" with "[$Hna Hℓ0]") as "Hna".
      { iNext. iLeft. iExists _, (RecV _ _ _). iFrame "Hℓ0". iSplit.
        1: iExists _; by iFrame "Hlv2".
        iExists _, _, _; iSplit; first done. iApply "Hcall". }
      iMod ("Hclose1" with "[$Hna Hℓ1]") as "Hna".
      { iNext. iExists _, _. iFrame "Hℓ1 Hvn Hsimvn". }
      wp_apply (wp_callback with "[$HGC $Hlv2 Hna]"); [done..| |].
      { iSplit; first iApply "Hlv1".
        iNext. iApply ("Hcall" with "Hv1 Hna"). }
      iIntros (θ' vret lvret wret) "(HGC & ((%v&Hv&->)&Hna) & _)".
      wp_pures.
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (w0) "(HGC&%Hw0)". iApply "Cont2".
      iApply ("Return" with "HGC (Cont Hna) [//] [//]").
    - wp_apply (wp_load with "Hℓ0"). iIntros "Hℓ0".
      wp_pures.
      iMod ("Hclose2" with "[$Hna Hℓ0]") as "Hna".
      { iNext. by iRight. }
      iMod ("Hclose1" with "[$Hna Hℓ1]") as "Hna".
      { iNext. iExists _, _. iFrame "Hℓ1 Hvn Hsimvn". }
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (w0) "(HGC&%Hw0)". iApply "Cont2".
      iApply ("Return" with "HGC (Cont Hna) [//] [//]").
  Qed.

  Lemma box_listen_correct :
    prims_proto Ψ ||- box_prog :: wrap_proto box_listen_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamedProto "Hproto".
    iSplit; first done.
    destruct lvs as [|lv [|lvb [|??]]]; try done.
    all: iEval (cbn) in "Hsim"; iDestruct "Hsim" as "(Hsimvl&Hsim)"; try done.
    all: iEval (cbn) in "Hsim"; iDestruct "Hsim" as "(Hsimvb&Hsim)"; try done.
    destruct ws as [|wl [|wb [|??]]]; decompose_Forall.
    iIntros (Φ'') "Cont2".
    wp_pure _.
    iDestruct "Hbox" as (γ ℓ) "(->&#Hγfgn&#Hinv1&#Hinv2)".
    iDestruct "Hsimvb" as "->".
    iMod (na_inv_acc_open with "Hinv2 Hna") as "HH". 1-2: solve_ndisj.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgn]"); [done..|].
    iIntros "(HGC&_)". iDestruct "HH" as "(HI2&Hna&Hclose2)".
    wp_pures.
    wp_bind (If _ _ _).
    iApply (wp_wand _ _ _ (λ _, (GC θ ∗ ∃ lv v, ℓ ↦roots lv ∗ lv ~~ v ∗ interp_arrow ⟨ ∅ , Ψ ⟩ interp interp_unit Δ v))%I
            with "[HGC HI2]"); first iDestruct "HI2" as "[(%lv2&%v2&Hℓ0&#Hlv2&#(%b1&%b2&%ec&->&#Hcall))|Hℓ0]".
    - iDestruct "Hlv2" as (γcb ->) "Hlv2".
      wp_apply (load_from_root with "[$HGC $Hℓ0]").
      iIntros (wcb) "(Hℓ0&HGC&%Hwcb)". inversion Hwcb; simplify_eq.
      wp_pure _. 1: by destruct a.
      wp_pures.
      wp_apply (store_to_root with "[$HGC $Hℓ0]"); first done.
      iIntros "($&Hℓ0)".
      iExists _, _. iFrame "Hℓ0 Hsimvl Hvl".
    - wp_apply (wp_load with "Hℓ0").
      iIntros "Hℓ0". wp_pures.
      wp_apply (wp_store with "Hℓ0").
      iIntros "Hℓ0". wp_pures.
      wp_apply (wp_registerroot with "[$HGC $Hℓ0]"); [done..|].
      iIntros "($&Hℓ0)".
      iExists _, _. iFrame "Hℓ0 Hsimvl Hvl".
    - iIntros (v) "(HGC&HInv)".
      iMod ("Hclose2" with "[$Hna HInv]") as "Hna".
      { iNext. by iLeft. }
      destruct v; wp_pures.
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (w0) "(HGC&%Hw0)". iApply "Cont2".
      iApply ("Return" with "HGC (Cont Hna) [//] [//]").
  Qed.

  End InPsi.

  Definition box_prog_spec_ML (Ψ : protocol ML_lang.val Σ) : protocol ML_lang.val Σ :=
    box_create_spec_ML Ψ ⊔ box_update_spec_ML Ψ ⊔ box_listen_spec_ML Ψ.


  Global Instance box_prog_spec_ML_contractive :
    Contractive (box_prog_spec_ML).
  Proof.
    solve_proper_prepare. do 2 try apply proto_join_ne;
    rewrite /box_create_spec_ML /box_update_spec_ML /box_listen_spec_ML /named.
    { do 12 first [f_equiv|intros ?]. f_contractive.
      repeat first [apply box_interp | f_equiv | intros ?]. }
    { do 16 first [f_equiv|intros ?]. f_contractive.
      repeat first [apply box_interp | f_equiv | intros ?]. }
    { do 15 first [f_equiv|intros ?]. 2: f_equiv.
      all: f_contractive.
      2: by apply box_interp. unfold interp_arrow; cbn.
      do 12 first [f_equiv | intros ?]. by apply wp_ne_proto. }
  Qed.

  Definition box_spec_ML := fixpoint (box_prog_spec_ML).
  Lemma box_spec_ML_unfold s vv Φ :
   (box_spec_ML s vv Φ ⊣⊢ box_prog_spec_ML (box_spec_ML) s vv Φ)%I.
  Proof.
    exact (fixpoint_unfold (box_prog_spec_ML) s vv Φ).
  Qed.

  Lemma buf_library_spec_ML_sim:
   (box_prog_spec_ML (box_spec_ML) ⊑ box_spec_ML)%I.
  Proof.
    iIntros (s vv Φ) "H". by iApply box_spec_ML_unfold.
  Qed.

  Lemma box_correct :
    prims_proto (box_spec_ML) ||- box_prog :: wrap_proto box_spec_ML.
  Proof.
    iIntros (s vv Φ) "H". iNamed "H".
    iPoseProof (box_spec_ML_unfold with "Hproto") as "[[Hproto|Hproto]|Hproto]".
    - iApply box_create_correct; repeat iExists _; iFrameNamed.
    - iApply box_update_correct; repeat iExists _; iFrameNamed.
    - iApply box_listen_correct; repeat iExists _; iFrameNamed.
  Qed.


  Definition ML_wrapper : ML_lang.expr := Λ: <>, pack: ( (λ: "v1", extern: "box_create" with ("v1")),
                                                         (λ: "v1" "v2", extern: "box_update" with ("v1", "v2")),
                                                         (λ: "v1" "v2", extern: "box_listen" with ("v1", "v2"))).

  Definition ML_type_inner (t:type) : type :=
    (TProd (TProd
       (* 'a -> 'a box *)
       (TArrow t (TVar 0))
       (* 'a -> 'a box -> unit *)
       (TArrow t (TArrow (TVar 0) TUnit)))
       (* ('a -> 'a unit) -> ('a box -> unit) *)
       (TArrow (TArrow t TUnit) (TArrow (TVar 0) TUnit))).

  Definition ML_type : type :=
    (* forall 'a, exists ' b == 'a box, ... *)
    TForall (TExist (ML_type_inner (TVar 1))).

  Import melocoton.ml_lang.proofmode melocoton.ml_lang.notation.
  Lemma sem_typed_box p P Γ :
    box_prog_spec_ML p.(penv_proto) ⊑ p.(penv_proto) →
    p.(penv_prog) = ∅ →
    ⊢ log_typed (p:=p) P Γ ML_wrapper ML_type.
  Proof.
    intros ??. iIntros "!>" (Δ vs) "#HΔ #Hvs".
    iIntros "?". wp_pures. iModIntro. iFrame.
    iExists _; iSplit; first done.
    iIntros "!>" (τ) "Htok".
    wp_pures. iModIntro. iFrame "Htok".
    iExists _; iSplit; first done.
    iExists (box_interp p.(penv_proto) (λne _, τ)%I Δ), _.
    iSplit; first done.
    iExists _, _; iSplit; first done; iSplit.
    1: iExists _, _; iSplit; first done; iSplit.
    all: iExists _, _, _; iSplit; first done; iIntros (v) "!> #Hv Htok".
    all: wp_pures.
    - wp_extern. 1: rewrite H1; done.
      iModIntro. iApply H0. iLeft. iLeft.
      iSplit; first done.
      iExists (λne _ : listO D, τ), Δ, _.
      iSplit; first done.
      iFrame "Htok Hv".
      iIntros "!> %vr [Htok #Hbox]".
      wp_pures. iModIntro. iFrame. iExists _; iSplit; first done. iFrame "Hbox".
    - iModIntro; iFrame; iExists _; iSplit; first done.
      iExists _, _, _; iSplit; first done.
      iIntros (v2) "!> #Hv2 Htok". wp_pures.
      wp_extern. 1: rewrite H1; done.
      iModIntro. iApply H0. iLeft. iRight.
      iSplit; first done.
      iExists (λne _ : listO D, τ), Δ, _, _.
      iSplit; first done.
      iFrame "Hv Hv2 Htok".
      iIntros "!> Htok".
      wp_pures. iModIntro. iFrame "Htok"; iExists _; iSplit; done.
    - iModIntro; iFrame; iExists _; iSplit; first done.
      iExists _, _, _; iSplit; first done.
      iIntros (v2) "!> #Hv2 Htok". wp_pures.
      wp_extern. 1: rewrite H1; done.
      iModIntro. iApply H0. iRight.
      iSplit; first done.
      iExists (λne _ : listO D, τ), Δ, _, _.
      iSplit; first done.
      iSplitL. { iFrame "Htok". destruct p as [p1 p2]. cbn in H1. subst p1.
                 iFrame "Hv Hv2". }
      iIntros "!> Htok".
      wp_pures. iModIntro. iFrame "Htok"; iExists _; iSplit; done.
  Qed.

  Definition box_client_1 : ML_lang.expr := λ: "box_abs",
    unpack: "box_abs" := (TApp "box_abs") in
    let: "mbox" := Fst (Fst "box_abs") (#0) in
    let: <> := Snd "box_abs" (λ: "v", Snd (Fst "box_abs") (#1) "mbox") "mbox" in
    #42.

  Lemma box_client_1_typed : 
    typed ∅ ∅ box_client_1 (TArrow ML_type TNat).
  Proof.
    econstructor; cbn in *.
    eapply (UnpackIn_typed _ _ _ _ _ (ML_type_inner TNat)).
    { cbn. eapply (TApp_typed _ _ _ (TExist (ML_type_inner (TVar 1))) TNat).
      repeat econstructor. }
    { cbn; rewrite fmap_insert fmap_empty insert_insert.
      repeat econstructor. }
  Qed.

  Definition box_client : ML_lang.expr := box_client_1 ML_wrapper.

  Lemma box_client_1_sem_typed :
    ⊢ log_typed (p:=⟨ ∅, box_spec_ML ⟩) ∅ ∅ box_client TNat.
  Proof.
    iApply (sem_typed_app (p:=⟨ ∅, box_spec_ML ⟩) with "[] []").
    - iApply fundamental. apply box_client_1_typed.
    - iApply sem_typed_box; cbn; try done.
      exact buf_library_spec_ML_sim.
  Qed.
End Proofs.


Lemma box_client_1_adequacy : 
umrel.trace (mlanguage.prim_step (combined_prog box_client box_prog))
  (LkCall "main" [], adequacy.σ_init)
  (λ '(e, σ), ∃ x, mlanguage.to_outcome e = Some (OVal (code_int x)) ∧ True).
Proof.
  eapply typed_adequacy_trace.
  intros Σ Hffi. split_and!.
  3: apply box_client_1_sem_typed.
  2: set_solver.
  3: apply box_correct.
  { iIntros (? Hn ?) "(% & H)". unfold prim_names in H.
    rewrite !dom_insert dom_empty /= in H.
    iDestruct (box_spec_ML_unfold with "H") as "[[H|H]|H]".
    all: iDestruct "H" as (?) "_"; exfalso; cbn in H; set_solver. }
  { iIntros (s vv Φ) "(%tl&%tr&%Heq&H1&H2&H3)".
    by rewrite lookup_empty in Heq. }
Qed.
