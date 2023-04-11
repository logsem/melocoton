From transfinite.base_logic.lib Require Import na_invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.interop Require Import basics basics_resources.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils prims_proto.
From melocoton.language Require Import weakestpre progenv.
From melocoton.c_interop Require Import rules notation.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.ml_lang Require primitive_laws proofmode.
From melocoton.ml_lang.logrel Require logrel fundamental.
From melocoton.c_lang Require Import notation proofmode derived_laws.

Definition tie_knot_code (l_arg x_arg : string) : C_lang.expr :=
  CAMLlocal: "l" in "l" <- l_arg ;;
  CAMLlocal: "x" in "x" <- x_arg ;;
  let: "f" := Field( *"l", #0) in
  let: "r" := call: &"callback" with ( "f", * "x") in
  CAMLreturn: "r" unregistering ["l", "x"].

Definition tie_knot_prog : lang_prog C_lang :=
  {[ "tie_knot" := Fun [BNamed "l_arg"; BNamed "x_arg"] (tie_knot_code "l_arg" "x_arg") ]}.

Section C_specs.
  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.

  Import melocoton.ml_lang.notation.
  Definition tie_knot_spec_ML (protoCB : (protocol ML_lang.val Σ)) : protocol ML_lang.val Σ :=
    λ s vv Φ,
    (∃ (l : loc) x b1 b2 (F : ML_lang.expr),
      "->" ∷ ⌜s = "tie_knot"⌝
    ∗ "->" ∷ ⌜vv = [ #l; x ]⌝
    ∗ "Hl" ∷ l ↦∗ [(RecV b1 b2 F)]
    ∗ "HWP" ∷ (l ↦∗ [(RecV b1 b2 F)] -∗ ▷ WP (RecV b1 b2 F) x at ⟨ ∅, protoCB ⟩ {{res, Φ res}}))%I.

  Lemma tie_knot_correct Ψ :
    prims_proto Ψ ||- tie_knot_prog :: wrap_proto (tie_knot_spec_ML Ψ).
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    iSplit; first done. iIntros (Φ'') "HΦ".
    destruct lvs as [|lvl [|lvx [|??]]]; try done.
    all: cbn; iDestruct "Hsim" as "([%γ [-> #Hγ]]&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(Hx&?)"; try done.
    destruct ws as [|wl [|wx [|??]]]; decompose_Forall.
    wp_call_direct.
    wp_apply (wp_CAMLlocal with "HGC"); [done..|].
    iIntros (ℓf) "(HGC&Hℓf)"; wp_pures.
    wp_apply (store_to_root with "[$HGC $Hℓf]"); [done..|].
    iIntros "(HGC&Hℓf)". wp_pures.
    wp_apply (wp_CAMLlocal with "HGC"); [done..|].
    iIntros (ℓx) "(HGC&Hℓx)"; wp_pures.
    wp_apply (store_to_root with "[$HGC $Hℓx]"); [done..|].
    iIntros "(HGC&Hℓx)". wp_pures.
    iMod (ml_to_mut with "[$HGC $Hl]") as "(HGC&(%lvs&%γ'&Hl&#Hγ'&Hlvs))".
    destruct lvs as [|lvf [|??]]; try done.
    all: cbn; iDestruct "Hlvs" as "([%γ'' [-> #Hγ'']]&?)"; try done.
    iAssert (⌜γ = γ'⌝)%I as %<-. {
      iDestruct (lloc_own_pub_inj with "Hγ Hγ' HGC") as "[? %]".
      iPureIntro. naive_solver.
    }
    wp_apply (load_from_root with "[$HGC $Hℓf]"); [done..|].
    iIntros (wf) "(Hℓf&HGC&%Hwf)".
    wp_apply (wp_readfield with "[$HGC $Hl]"); [done..|].
    iIntros (? wfaux) "(HGC&Hl&%Heq&%Hγaux)"; cbv in Heq; simplify_eq. wp_pures.
    wp_apply (load_from_root with "[$HGC $Hℓx]"); [done..|].
    iIntros (wx') "(Hℓx&HGC&%Hwx)".
    iMod (mut_to_ml _ [RecV _ _ _] with "[$HGC $Hl]") as "[HGC (%l'&Hl&#Hγ''')]".
    { cbn. eauto with iFrame. }
    iAssert (⌜l' = l⌝)%I as %<-. {
      iDestruct (lloc_own_pub_inj with "Hγ' Hγ''' HGC") as "[? %]".
      iPureIntro. naive_solver.
    }
    wp_apply (wp_callback with "[$HGC $Hx $Hγ'' HWP Hl]"); [done.. | |].
    { by iApply "HWP". }
    iIntros (θ' vret lvret wret) "(HGC&HΦ'&Hvret&%)". wp_pures.
    wp_apply (wp_CAMLunregister1 with "[$HGC $Hℓf]"); [try done..|].
    iIntros "HGC"; wp_pure _.
    wp_apply (wp_CAMLunregister1 with "[$HGC $Hℓx]"); [try done..|].
    iIntros "HGC"; wp_pure _.
    iModIntro. iApply "HΦ". iApply ("Cont" with "HGC HΦ' Hvret [//]").
  Qed.

  Global Instance tie_knot_spec_ML_contractive :
    Contractive (tie_knot_spec_ML).
  Proof.
    solve_proper_prepare. unfold named.
    do 14 f_equiv. f_contractive.
    by eapply wp_ne_proto.
  Qed.

End C_specs.

Section ML_code.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.
  Context `{!logrel.logrelG Σ}.
  Import melocoton.ml_lang.notation melocoton.ml_lang.lang_instantiation
         melocoton.ml_lang.primitive_laws melocoton.ml_lang.proofmode.

  (* TODO: We cannot Import logrel as this breaks notations so we redeclare na_tok. *)
  Notation na_tok := (na_own logrel.logrel_nais ⊤).

  Definition knot_code : MLval :=
    λ: "f",
    let: "l" := ref (rec: <> "x" := "x") in
    "l" <- (λ: "x", "f" (λ: "x", extern: "tie_knot" with ("l", ML_lang.Var "x")) "x");;
    (λ: "x", extern: "tie_knot" with ("l", "x")).

  Lemma knot_code_spec p (f : val) :
    tie_knot_spec_ML p.(penv_proto) ⊑ p.(penv_proto) →
    p.(penv_prog) = ∅ →
    ⊢ WP knot_code f at p {{ rc, ∃ b1 b2 e, ⌜rc = RecV b1 b2 e⌝ ∗
    □ (∀ Φ Ψ,
      □ (∀ rec : val, (∃ b1 b2 e, ⌜rec = RecV b1 b2 e⌝) -∗ □ (∀ v : val, Ψ v -∗ na_tok -∗ WP rec v at p {{ v, Φ v ∗ na_tok }}) -∗
         ∀ v : val, Ψ v -∗ na_tok -∗ WP f rec v at p {{ v, Φ v ∗ na_tok }}) -∗
      ∀ (v : val), Ψ v -∗ na_tok -∗ WP (rc : val) v at p {{ v, Φ v ∗ na_tok }} )
    }}.
  Proof.
    intros Hproto ?. destruct p. simplify_eq/=. unfold knot_code. wp_pures.
    wp_apply (wp_allocN); [done..|] => /=.
    iIntros (l) "[Hl _]". wp_pures.
    wp_apply (wp_store with "Hl").
    iIntros "Hl". wp_pures.
    iMod (na_inv_alloc logrel.logrel_nais _ (nroot .@ "knot") with "[Hl]") as "#HL".
    { iNext. iExact "Hl". }
    iExists _, _, _; iModIntro; iSplit; first done.
    iIntros "!>" (Φ Ψ) "#Hf". iIntros (v) "HΨ Htok". wp_pures.
    iLöb as "IH" forall (v).
    wp_extern.
    iMod (na_inv_acc_open_timeless with "HL Htok") as "(Hl&Htok&Hclose)"; [done..|].
    iModIntro. simpl. iApply Hproto. unfold tie_knot_spec_ML.
    iExists _, _, _, _, _. iFrame. iSplit; [done|]. iSplit; [done|]. unfold named.
    iIntros "Hl !>". wp_pures.
    iMod ("Hclose" with "[$Hl $Htok]") as "Htok".
    iApply (wp_wand (val:=val) with "[-]"). (* TODO: Why does wp_wand need (val:=val) ? *)
    - iApply ("Hf" with "[] [] HΨ Htok"). 1: by do 3 iExists _.
      iIntros "!>" (v') "HΨ Htok". wp_pures.
      iApply ("IH" with "HΨ Htok").
    - iIntros (v') "Hv'". wp_pures. by iModIntro.
  Qed.


  Import melocoton.ml_lang.logrel.logrel melocoton.ml_lang.logrel.fundamental.

  Lemma sem_typed_knot p P Γ τ1 τ2 :
    tie_knot_spec_ML p.(penv_proto) ⊑ p.(penv_proto) →
    p.(penv_prog) = ∅ →
    ⊢ log_typed (p:=p) P Γ knot_code
      (* ((τ1 -> τ2) -> (τ1 -> τ2)) -> (τ1 -> τ2) *)
      (TArrow (TArrow (TArrow τ1 τ2) (TArrow τ1 τ2)) (TArrow τ1 τ2)).
  Proof.
    intros ??. iIntros "!>" (Δ vs) "HΔ Hvs".
    iIntros "?". simpl. wp_pures. iModIntro. iFrame. do 3 iExists _; iSplit; first done.
    iIntros "!>" (f) "#(%bb1&%bb2&%ee1&%Heqf&Hf) Htok".
    iApply (wp_wand (val:=val)). { by iApply knot_code_spec. }
    iIntros (rc) "#(%b1&%b2&%ee&%Heq&Hrc)". iFrame. do 3 iExists _; iSplit; first done.
    iIntros "!>" (v) "#Hv Htok".
    iApply ("Hrc" $! ((⟦ τ2 ⟧ p) Δ) ((⟦ τ1 ⟧ p) Δ) with "[] [//] Htok").
    iIntros "!>" (rec) "(%br1&%br2&%er&->) #Hx".
    iIntros (v') "#Hv' Htok".
    wp_bind (App f _).
    iApply (wp_wand (val:=val) with "[Htok] []").
    { iApply "Hf"; [|done]. iExists _, _, _. iSplit; first done. iIntros "!>" (?) "#? Htok". by iApply "Hx". }
    iIntros (?) "[#(%&%&%&_&Hwp') Htok]".
    by iApply ("Hwp'").
  Qed.

End ML_code.
