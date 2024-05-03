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

Definition listener_create_code : C_lang.expr :=
  let: "k" := malloc (#1) in
  "k" <- #LitNull ;;
  let: "bk" := caml_alloc_custom ( ) in
  (Custom_contents ( "bk" ) := "k") ;;
  "bk".

Definition listener_notify_code (v' b : C_lang.expr) : C_lang.expr :=
  let: "k" := Custom_contents (b) in
  let: "cb" := *"k" in
  (if: "cb" ≠ #LitNull
     then call: &"callback" with ( "cb", v')
     else Skip) ;;
  Val_int (#0) .

Definition listener_listen_code (l b : C_lang.expr) : C_lang.expr :=
  let: "k" := Custom_contents (b) in
  let: "b'" := *"k" = #LitNull in
  "k" <- l ;;
  (if: "b'" then call: &"registerroot" with ("k") else Skip);;
  Val_int (#0) .

Definition listener_unlisten_code (b : C_lang.expr) : C_lang.expr :=
  let: "k" := Custom_contents (b) in
  (if: *"k" ≠ #LitNull then call: &"unregisterroot" with ("k") else Skip);;
  "k" <- #LitNull ;;
  Val_int (#0) .

Definition listener_prog : lang_prog C_lang :=
  {[ "listener_create" := Fun [BNamed "u"] listener_create_code;
     "listener_notify" := Fun [BNamed "v'"; BNamed "b"] (listener_notify_code "v'" "b");
     "listener_listen" := Fun [BNamed "l"; BNamed "b"] (listener_listen_code "l" "b");
     "listener_unlisten" := Fun [BNamed "b"] (listener_unlisten_code "b") ]}.

Section Proofs.
  Import melocoton.ml_lang.notation.
  Import fundamental logrel typing.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ}.
  Context `{!primitive_laws.heapG_ML Σ, !wrapperG Σ, !logrelG Σ}.


  Notation D := (persistent_predO val (iPropI Σ)).
  Implicit Types τi : D.
  Implicit Types Δ : listO D.
  Implicit Types interp : listO D -n> D.

  Program Definition listener_invariant a : D -n> iProp Σ := (λne (interp:D),
    (∃ lv v, a ↦roots lv ∗ lv ~~ v ∗ interp v) ∨ a ↦C (#C LitNull))%I.
  Solve Obligations with solve_proper.

  Program Definition listener_interp : (protocol ML_lang.val Σ) -n> (listO D -n> D) -d> listO D -n> D := λne Ψ, λ interp, λne Δ, PersPred (
    λ v, ∃ γ (a:addr), ⌜v = #(LitForeign γ)⌝ ∗ γ ↦foreign[Immut] (#C a) ∗
           na_inv logrel_nais (nroot .@ "listener" .@ γ)
             (listener_invariant a (interp_arrow ⟨ ∅ , Ψ ⟩ interp interp_unit Δ)))%I.
  Next Obligation. solve_proper. Qed.
  Next Obligation.
    solve_proper_prepare.
    do 26 first [intros ? | f_equiv].
    by apply wp_ne_proto.
  Qed.

  Section InPsi.
  Context (Ψ : protocol ML_lang.val Σ).

  Import melocoton.ml_lang.notation.

  Definition listener_create_spec_ML : protocol ML_lang.val Σ :=
    !! interp Δ
    {{ "Hna" ∷ na_tok }}
      "listener_create" with [ #() ]
    {{ vr, RET vr; na_tok ∗ listener_interp Ψ interp Δ vr }}.
  Definition listener_notify_spec_ML : protocol ML_lang.val Σ :=
    !! interp Δ vn vb
    {{
       "#Hvn" ∷ interp Δ vn ∗
       "Hna" ∷ na_tok ∗
       "#Hbox" ∷ ▷ listener_interp Ψ interp Δ vb
    }}
      "listener_notify" with [ vn; vb ]
    {{ RET #(); na_tok }}.
  Definition listener_listen_spec_ML : protocol ML_lang.val Σ :=
    !! interp Δ vl vb
    {{
       "#Hvl" ∷ ▷ interp_arrow ⟨ ∅ , Ψ ⟩ interp interp_unit Δ vl ∗
       "#Hbox" ∷ ▷ listener_interp Ψ interp Δ vb ∗
       "Hna" ∷ na_tok
    }}
      "listener_listen" with [ vl; vb ]
    {{ RET #(); na_tok }}.
  Definition listener_unlisten_spec_ML : protocol ML_lang.val Σ :=
    !! interp Δ vb
    {{
       "#Hbox" ∷ ▷ listener_interp Ψ interp Δ vb ∗
       "Hna" ∷ na_tok
    }}
      "listener_unlisten" with [ vb ]
    {{ RET #(); na_tok }}.

  Import melocoton.c_lang.primitive_laws melocoton.c_lang.proofmode.

  Local Opaque listener_interp.

  Lemma listener_create_correct :
    prims_proto Ψ ||- listener_prog :: wrap_proto listener_create_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamedProto "Hproto".
    iSplit; first done.
    destruct lvs as [|lvl [|??]]; try done.
    all: iEval (cbn) in "Hsim"; iDestruct "Hsim" as "(->&Hsim)"; try done.
    destruct ws as [|wv [|??]]; decompose_Forall.
    iIntros (Φ'') "Cont2".
    wp_pure _.
    wp_apply (wp_Malloc); [done..|].
    change (Z.to_nat 1) with 1. cbn.
    iIntros (a) "(Ha&_)".
    replace ((a +ₗ 0%nat)) with a by by rewrite loc_add_0.
    wp_pures.
    wp_apply (wp_store with "Ha"). iIntros "Ha".
    wp_pures.
    wp_apply (wp_alloc_foreign with "HGC"); [done..|].
    iIntros (θ1 γ w) "(HGC&Hγfgn&%Hrepr)".
    wp_pures.
    wp_apply (wp_write_foreign with "[$HGC $Hγfgn]"); [done..|].
    iIntros "(HGC&Hγfgn)". wp_pures.
    iDestruct "Hγfgn" as "(Hγfgn'&Hγfresh)".
    iMod (na_inv_alloc logrel_nais _ _ (listener_invariant a _) with "[Ha]") as "#Hinv".
    { iNext. iRight. iFrame "Ha". }
    iMod (freeze_foreign_to_immut γ θ1 _ with "[$]") as "(HGC&#Hγfgn')".
    iModIntro. iApply "Cont2". iApply ("Return" $! θ1 (#(LitForeign γ)) with "HGC [-] [] []").
    2,3: done.
    iApply "Cont". iFrame "Hna". iExists γ, a.
    iSplit; first done. iSplitL.
    { iApply "Hγfgn'". }
    iFrame "Hinv".
  Qed.

  Lemma listener_notify_correct :
    prims_proto Ψ ||- listener_prog :: wrap_proto listener_notify_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamedProto "Hproto".
    iSplit; first done.
    destruct lvs as [|lvn [|lvb [|??]]]; try done.
    all: cbn; iDestruct "Hsim" as "(Hsimvn&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(Hsimvb&Hsim)"; try done.
    destruct ws as [|wn [|wb [|??]]]; decompose_Forall.
    iIntros (Φ'') "Cont2".
    wp_pure _.
    Local Transparent listener_interp.
    iDestruct "Hbox" as (γ a) "(->&#Hγfgn&#Hinv)".
    iDestruct "Hsimvb" as "->".
    iMod (na_inv_acc_open with "Hinv Hna") as "HH". 1-2: solve_ndisj.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgn]"); [done..|].
    iIntros "(HGC&_)". wp_pures.
    iDestruct "HH" as "([(%lv&%v&Ha&#Hsimvlv&#Hinterp)|Hnull]&Hna&Hclose)".
    - wp_apply (load_from_root with "[$HGC $Ha]").
      iIntros (wcb) "(Ha&HGC&%Hcb)". wp_pures.
      iDestruct "Hinterp" as (b1 b2 e ->) "#Hinterp".
      iDestruct "Hsimvlv" as (γclos ->) "Hclos".
      inversion Hcb; simplify_eq.
      wp_pure _.
      { by destruct a0. }
      wp_pures.
      iMod ("Hclose" with "[$Hna Ha]") as "Hna".
      { iNext. iLeft. iExists _, (RecV b1 b2 e). iFrame "Ha". iSplit.
        + iExists _; by iSplit.
        + iExists _, _, _; by repeat iSplit. }
      wp_apply (wp_callback with "[$HGC $Hclos $Hsimvn Hinterp Hna]"); [try done..|].
      { iNext. by iApply "Hinterp". }
      iIntros (θ' vret lvret wret) "(HGC & [_ Hna] & Hsimret & %)".
      wp_pures. wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (?) "[HGC %HH]". inversion HH; simplify_eq.
      iApply "Cont2". iApply ("Return" with "HGC [Cont Hna] [] []").
      1: by iApply "Cont". 1,2: by iPureIntro.
    - wp_apply (wp_load with "[$Hnull]"). iIntros "Hnull".
      wp_pures.
      iMod ("Hclose" with "[$Hna Hnull]") as "Hna".
      { iNext. iRight. iFrame. }
      wp_apply (wp_int2val with "HGC"); [done..|].
      iIntros (?) "[HGC %HH]". inversion HH; simplify_eq.
      iApply "Cont2". iApply ("Return" with "HGC [Cont Hna] [] []").
      1: by iApply "Cont". 1,2: by iPureIntro.
  Qed.

  Local Opaque listener_interp.

  Lemma listener_listen_correct :
    prims_proto Ψ ||- listener_prog :: wrap_proto listener_listen_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamedProto "Hproto".
    iSplit; first done.
    destruct lvs as [|lv [|lvb [|??]]]; try done.
    all: cbn; iDestruct "Hsim" as "(Hsimvl&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(Hsimvb&Hsim)"; try done.
    destruct ws as [|wl [|wb [|??]]]; decompose_Forall.
    iIntros (Φ'') "Cont2".
    wp_pure _.
    Local Transparent listener_interp.
    iDestruct "Hbox" as (γ a) "(->&#Hγfgn&#Hinv)".
    iDestruct "Hsimvb" as "->".
    iMod (na_inv_acc_open with "Hinv Hna") as "HH". 1-2: solve_ndisj.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgn]"); [done..|].
    iIntros "(HGC&_)".
    iDestruct "HH" as "([(%lvc&%vc&Ha&#Hsimvlvc&#Hinterp)|Hnull]&Hna&Hclose)".
    - iDestruct "Hinterp" as (b1 b2 e ->) "#Hinterp".
      iDestruct "Hsimvlvc" as (γclos ->) "Hclos".
      wp_pures.
      wp_apply (load_from_root with "[$HGC $Ha]"); [done..|]. iIntros (wcbo) "(Ha&HGC&%Hreprcb)".
      inversion Hreprcb; simplify_eq.
      wp_pures. wp_pure _.
      { by destruct a0. }
      wp_pures.
      wp_apply (store_to_root with "[$HGC $Ha]"); [done..|]. iIntros "[HGC Ha]".
      wp_pures.
      iMod ("Hclose" with "[$Hna Ha]") as "Hna".
      { iNext. iLeft. iExists _, _. iFrame "Ha Hvl Hsimvl". }
      wp_apply (wp_int2val with "HGC"); [done..|]. iIntros (?) "[HGC %]".
      iApply "Cont2". iApply ("Return" with "HGC [Cont Hna]").
      1: by iApply "Cont". 1,2: by iPureIntro.
    - wp_pures.
      wp_apply (wp_load with "Hnull"); iIntros "Hnull".
      wp_pures.
      wp_apply (wp_store with "Hnull"); iIntros "Hnull".
      wp_pures.
      wp_apply (wp_registerroot with "[$HGC $Hnull]"); [try done..|];
      iIntros "(HGC&Hroot)".
      wp_pures.
      iMod ("Hclose" with "[$Hna Hroot]") as "Hna".
      { iNext. iLeft. iExists _, _. iFrame "Hroot Hvl Hsimvl". }
      wp_apply (wp_int2val with "HGC"); [done..|]. iIntros (?) "[HGC %]".
      iApply "Cont2". iApply ("Return" with "HGC [Cont Hna]").
      1: by iApply "Cont". 1,2: by iPureIntro.
  Qed.

  Lemma listener_unlisten_correct :
    prims_proto Ψ ||- listener_prog :: wrap_proto listener_unlisten_spec_ML.
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamedProto "Hproto".
    iSplit; first done.
    destruct lvs as [|lv [|lvb [|??]]]; try done.
    all: iEval (cbn) in "Hsim"; iDestruct "Hsim" as "(Hsimvb&Hsim)"; try done.
    destruct ws as [|wl [|wb [|??]]]; decompose_Forall.
    iIntros (Φ'') "Cont2".
    wp_pure _.
    Local Transparent listener_interp.
    iDestruct "Hbox" as (γ a) "(->&#Hγfgn&#Hinv)".
    iDestruct "Hsimvb" as "->".
    iMod (na_inv_acc_open with "Hinv Hna") as "HH". 1-2: solve_ndisj.
    wp_apply (wp_read_foreign with "[$HGC $Hγfgn]"); [done..|].
    iIntros "(HGC&_)".
    iDestruct "HH" as "([(%lvc&%vc&Ha&#Hsimvlvc&#Hinterp)|Hnull]&Hna&Hclose)".
    - iDestruct "Hinterp" as (b1 b2 e ->) "#Hinterp".
      iDestruct "Hsimvlvc" as (γclos ->) "Hclos".
      wp_pures.
      wp_apply (load_from_root with "[$HGC $Ha]"); [done..|]. iIntros (wcbo) "(Ha&HGC&%Hreprcb)".
      inversion Hreprcb; simplify_eq.
      wp_pures. wp_pure _.
      { by destruct a0. }
      wp_pures.
      wp_apply (wp_unregisterroot with "[$HGC $Ha]"); [done..|]. iIntros (w) "(HGC&Ha&_)".
      wp_pures.
      wp_apply (wp_store with "Ha"); iIntros "Ha".
      iMod ("Hclose" with "[$Hna Ha]") as "Hna".
      { iNext. iRight. iFrame. } wp_pures.
      wp_apply (wp_int2val with "HGC"); [done..|]. iIntros (?) "[HGC %]".
      iApply "Cont2". iApply ("Return" with "HGC [Cont Hna]").
      1: by iApply "Cont". 1,2: by iPureIntro.
    - wp_pures.
      wp_apply (wp_load with "Hnull"); iIntros "Hnull".
      wp_pures.
      wp_apply (wp_store with "Hnull"); iIntros "Hnull".
      wp_pures.
      iMod ("Hclose" with "[$Hna Hnull]") as "Hna".
      { iNext. iRight. iFrame. }
      wp_apply (wp_int2val with "HGC"); [done..|]. iIntros (?) "[HGC %]".
      iApply "Cont2". iApply ("Return" with "HGC [Cont Hna]").
      1: by iApply "Cont". 1,2: by iPureIntro.
  Qed.

  End InPsi.

  Definition listener_prog_spec_ML (Ψ : protocol ML_lang.val Σ) : protocol ML_lang.val Σ :=
    listener_create_spec_ML Ψ ⊔ listener_notify_spec_ML Ψ ⊔ listener_listen_spec_ML Ψ ⊔ listener_unlisten_spec_ML Ψ.


  Global Instance listener_prog_spec_ML_contractive :
    Contractive (listener_prog_spec_ML).
  Proof.
    solve_proper_prepare. do 3 try apply proto_join_ne;
    rewrite /listener_create_spec_ML /listener_notify_spec_ML /listener_listen_spec_ML /listener_unlisten_spec_ML /named.
    { do 10 first [f_equiv|intros ?]. f_contractive.
      repeat first [apply listener_interp | f_equiv | intros ?]. }
    { do 16 first [f_equiv|intros ?]. f_contractive.
      repeat first [apply listener_interp | f_equiv | intros ?]. }
    { do 15 first [f_equiv|intros ?]. 2: f_equiv.
      all: f_contractive.
      2: by apply listener_interp. unfold interp_arrow; cbn.
      do 12 first [f_equiv | intros ?]. by apply wp_ne_proto. }
    { do 13 first [f_equiv|intros ?]. f_contractive.
      repeat first [apply listener_interp | f_equiv | intros ?]. }
  Qed.

  Definition listener_spec_ML := fixpoint (listener_prog_spec_ML).
  Lemma listener_spec_ML_unfold s vv Φ :
   (listener_spec_ML s vv Φ ⊣⊢ listener_prog_spec_ML (listener_spec_ML) s vv Φ)%I.
  Proof.
    exact (fixpoint_unfold (listener_prog_spec_ML) s vv Φ).
  Qed.
  Lemma buf_library_spec_ML_sim:
   (listener_prog_spec_ML (listener_spec_ML) ⊑ listener_spec_ML)%I.
  Proof.
    iIntros (s vv Φ) "H". by iApply listener_spec_ML_unfold.
  Qed.

  Lemma listener_correct :
    prims_proto (listener_spec_ML) ||- listener_prog :: wrap_proto listener_spec_ML.
  Proof.
    iIntros (s vv Φ) "H". iNamed "H".
    iPoseProof (listener_spec_ML_unfold with "Hproto") as "[[[Hproto|Hproto]|Hproto]|Hproto]".
    - iApply listener_create_correct; repeat iExists _; iFrameNamed.
    - iApply listener_notify_correct; repeat iExists _; iFrameNamed.
    - iApply listener_listen_correct; repeat iExists _; iFrameNamed.
    - iApply listener_unlisten_correct; repeat iExists _; iFrameNamed.
  Qed.


  Definition ML_wrapper : ML_lang.expr := Λ: <>, pack: ( (λ: "v1", extern: "listener_create" with ("v1")),
                                                         (λ: "v1" "v2", extern: "listener_notify" with ("v1", "v2")),
                                                         (λ: "v1" "v2", extern: "listener_listen" with ("v1", "v2")),
                                                         (λ: "v1", extern: "listener_unlisten" with ("v1"))).


  Definition ML_type_inner (t:type) : type :=
    (TProd (TProd (TProd
       (* unit -> 'a listener *)
       (TArrow TUnit (TVar 0))
       (* 'a -> 'a listener -> unit *)
       (TArrow t (TArrow (TVar 0) TUnit)))
       (* ('a -> unit) -> ('a listener -> unit) *)
       (TArrow (TArrow t TUnit) (TArrow (TVar 0) TUnit)))
       (* ('a listener -> unit) *)
       ((TArrow (TVar 0) TUnit))).

  Definition ML_type : type :=
    (* forall 'a, exists ' b == 'a listener, ... *)
    TForall (TExist (ML_type_inner (TVar 1))).


  Import melocoton.ml_lang.proofmode melocoton.ml_lang.notation.
  Lemma sem_typed_listener p P Γ :
    listener_prog_spec_ML p.(penv_proto) ⊑ p.(penv_proto) →
    p.(penv_prog) = ∅ →
    ⊢ log_typed (p:=p) P Γ ML_wrapper ML_type.
  Proof.
    intros ??. iIntros "!>" (Δ vs) "#HΔ #Hvs".
    iIntros "?". wp_pures. iModIntro. iFrame. iIntros "!>" (τ) "Htok".
    wp_pures. iModIntro. iFrame "Htok".
    iExists (listener_interp p.(penv_proto) (λne _, τ)%I Δ), _.
    iSplit; first done.
    iExists _, _; iSplit; first done; iSplit.
    1: iExists _, _; iSplit; first done; iSplit.
    1: iExists _, _; iSplit; first done; iSplit.
    all: iExists _, _, _; iSplit; first done; iIntros (v) "!> #Hv Htok".
    all: wp_pures.
    - wp_extern. 1: rewrite H1; done. cbn. unfold env_lookup.
      iDestruct "Hv" as %->.
      iModIntro. iApply H0. iLeft. iLeft. iLeft. iSplit; first done.
      iExists (λne _ : listO D, τ), Δ.
      iSplit; first done. iFrame "Htok".
      iIntros "!> %vr (Htok & #Hbox)".
      wp_pures. iModIntro. iFrame "Htok Hbox".
    - iModIntro; iFrame; iExists _, _, _; iSplit; first done.
      iIntros (v2) "!> #Hv2 Htok". wp_pures.
      wp_extern. 1: rewrite H1; done.
      iModIntro. iApply H0. iLeft. iLeft. iRight.
      iSplit; first done.
      iExists (λne _ : listO D, τ), Δ, _, _.
      iSplit; first done. iFrame "Htok Hv Hv2".
      iIntros "!> Htok".
      wp_pures. iModIntro. iFrame "Htok". done.
    - iModIntro; iFrame; iExists _, _, _; iSplit; first done.
      iIntros (v2) "!> #Hv2 Htok". wp_pures.
      wp_extern. 1: rewrite H1; done.
      iModIntro. iApply H0. iLeft. iRight. iSplit; first done.
      iExists (λne _ : listO D, τ), Δ, _, _.
      iSplit; first done.
      iSplitL.
      { destruct p as [p1 p2]; cbn in H1; subst p1. iFrame "Hv Hv2 Htok". }
      iIntros "!> Htok".
      wp_pures. iModIntro. iFrame "Htok". done.
    - wp_extern. 1: rewrite H1; done. cbn. unfold env_lookup.
      iModIntro. iApply H0. iRight. iSplit; first done.
      iExists (λne _ : listO D, τ), Δ. iExists _.
      iSplit; first done. iFrame "Htok Hv".
      iIntros "!> Htok". wp_pures. iModIntro. iFrame. done.
  Qed.

  Definition listener_client_1 : ML_lang.expr := λ: "l",
    unpack: "l" := (TApp "l") in
    let: "ml" := Fst (Fst (Fst "l")) (#()) in
    let: <> := Snd (Fst "l") (λ: "v", Snd (Fst (Fst "l")) (#1) "ml") "ml" in
    #42.

  Lemma listener_client_1_typed :
    typed ∅ ∅ listener_client_1 (TArrow ML_type TNat).
  Proof.
    econstructor; cbn in *.
    eapply (UnpackIn_typed _ _ _ _ _ (ML_type_inner TNat)).
    { cbn. eapply (TApp_typed _ _ _ (TExist (ML_type_inner (TVar 1))) TNat).
      repeat econstructor. }
    { cbn; rewrite fmap_insert fmap_empty insert_insert.
      repeat econstructor. }
  Qed.

  Definition listener_client : ML_lang.expr := listener_client_1 ML_wrapper.

  Lemma listener_client_1_sem_typed :
    ⊢ log_typed (p:=⟨ ∅, listener_spec_ML ⟩) ∅ ∅ listener_client TNat.
  Proof.
    iApply (sem_typed_app (p:=⟨ ∅, listener_spec_ML ⟩) with "[] []").
    - iApply fundamental. apply listener_client_1_typed.
    - iApply sem_typed_listener; cbn; try done.
      exact buf_library_spec_ML_sim.
  Qed.
End Proofs.


Lemma listener_client_1_adequacy :
umrel.trace (mlanguage.prim_step (combined_prog listener_client listener_prog))
  (LkCall "main" [], adequacy.σ_init)
  (λ '(e, σ), ∃ x, mlanguage.to_val e = Some (code_int x) ∧ True).
Proof.
  eapply typed_adequacy_trace.
  intros Σ Hffi. split_and!.
  3: apply listener_client_1_sem_typed.
  2: set_solver.
  3: apply listener_correct.
  { iIntros (? Hn ?) "(% & H)". unfold prim_names in H.
    rewrite !dom_insert dom_empty /= in H.
    iDestruct (listener_spec_ML_unfold with "H") as "[[[H|H]|H]|H]".
    all: iDestruct "H" as (?) "_"; exfalso; cbn in H; set_solver. }
  { iIntros (s vv Φ) "(%tl&%tr&%Heq&H1&H2&H3)".
    by rewrite lookup_empty in Heq. }
Qed.

(*Print Assumptions listener_client_1_adequacy.*)
(* Should print the assumed axioms, which are:
   - Prop Extensionality
   - Proof Irrelevance
   - (dependent) Fun Ext
   - Excluded Middle
   - Epsilon (i.e. computable choice)
*)
