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
From melocoton.examples Require Import compression.

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
  Definition tie_knot_spec_ML (protoCB : (protocol ML_lang.val Σ)) E : protocol ML_lang.val Σ :=
    λ s vv Φ,
    (∃ (l : loc) x b1 b2 (F : ML_lang.expr),
      "->" ∷ ⌜s = "tie_knot"⌝
    ∗ "->" ∷ ⌜vv = [ #l; x ]⌝
    ∗ "Hl" ∷ l ↦∗ [(RecV b1 b2 F)]
    ∗ "HWP" ∷ (l ↦∗ [(RecV b1 b2 F)] -∗ WP (RecV b1 b2 F) x @ ⟨ ∅, protoCB ⟩ ; E {{res, Φ res}}))%I.

  Lemma tie_knot_correct E Ψ :
    prims_proto E Ψ ||- tie_knot_prog @ E :: wrap_proto (tie_knot_spec_ML Ψ E).
  Proof.
    iIntros (s ws Φ) "H". iNamed "H". iNamed "Hproto".
    cbn. unfold progwp, tie_knot_prog. solve_lookup_fixed.
    destruct lvs as [|lvl [|lvx [|??]]]; try done.
    all: cbn; iDestruct "Hsim" as "([%γ [-> #Hγ]]&Hsim)"; try done.
    all: cbn; iDestruct "Hsim" as "(Hx&?)"; try done.
    destruct ws as [|wl [|wx [|??]]]; try (eapply Forall2_length in Hrepr; cbn in Hrepr; done).
    eapply Forall2_cons in Hrepr as (Hrepri&Hrepr).
    eapply Forall2_cons in Hrepr as (Hreprj&Hrepr).
    cbn. iExists _. iSplit; first done.
    iExists _. cbn. solve_lookup_fixed. iSplit; first done. iNext.
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
    iModIntro. iApply ("Cont" with "HGC HΦ' Hvret [//]").
  Qed.
End C_specs.

Section ML_code.

  Context `{SI:indexT}.
  Context `{!heapG_C Σ, !heapG_ML Σ, !invG Σ, !primitive_laws.heapG_ML Σ, !wrapperG Σ}.
  Import melocoton.ml_lang.notation melocoton.ml_lang.lang_instantiation
         melocoton.ml_lang.primitive_laws melocoton.ml_lang.proofmode.

  (* We cannot Import logrel as this breaks notations. *)
  Notation na_tok := (na_own logrel.logrel_nais ⊤).

  Context (protoCB : (protocol ML_lang.val Σ)).
  Context `{!logrel.logrelG Σ}.

  Definition ML_knot_env : prog_environ ML_lang Σ := {|
    penv_prog  := ∅ ;
    penv_proto := tie_knot_spec_ML protoCB ⊤ ⊔ protoCB |}.

  Definition knot_code : MLval :=
    λ: "f",
    let: "l" := ref (rec: <> "x" := "x") in
    "l" <- (λ: "x", "f" (λ: "x", extern: "tie_knot" with ("l", ML_lang.Var "x")) "x");;
    (λ: "x", extern: "tie_knot" with ("l", "x")).

  Lemma knot_code_spec (f : val) :
    ⊢ WP knot_code f @ ML_knot_env ; ⊤ {{ rc,
    □ (∀ Φ Ψ,
    □ (∀ rec : val, □ (∀ v : val, Ψ v -∗ na_tok -∗ WP rec v @ ML_knot_env; ⊤ {{ v, na_tok ∗ Φ v }}) -∗
       ∀ v : val, Ψ v -∗ na_tok -∗ WP f rec v @ ML_knot_env; ⊤ {{ v, na_tok ∗ Φ v }}) -∗
    ∀ (v : val), Ψ v -∗ na_tok -∗ WP (rc : val) v @ ML_knot_env ; ⊤ {{ v, na_tok ∗ Φ v }} )
 }}.
  Proof.
    unfold knot_code. wp_pures.
    wp_apply (wp_allocN); [done..|] => /=.
    iIntros (l) "[Hl _]". wp_pures.
    wp_apply (wp_store with "Hl").
    iIntros "Hl". wp_pures.
    iMod (na_inv_alloc logrel.logrel_nais _ (nroot .@ "knot") with "[Hl]") as "#HL".
    { iNext. iExact "Hl". }
    iIntros "!> !>" (Φ Ψ) "#Hf". iIntros (v) "HΨ Htok". wp_pures.
    iLöb as "IH" forall (v).
    wp_extern.
    iMod (na_inv_acc_open_timeless with "HL Htok") as "(Hl&Htok&Hclose)"; [done..|].
    iModIntro. simpl. iLeft. unfold tie_knot_spec_ML.
    iExists _, _, _, _, _. iFrame. iSplit; [done|]. iSplit; [done|]. unfold named.
    iIntros "Hl". wp_pures.
    iMod ("Hclose" with "[$Hl $Htok]") as "Htok".
    (* TODO: make ML_knot_env recursive to fix this *)
    change_no_check ({| penv_prog := ∅; penv_proto := protoCB |}) with ML_knot_env.
    iApply (wp_wand (val:=val) with "[-]").
    - iApply ("Hf" with "[] HΨ Htok"). iIntros "!>" (v') "HΨ Htok". wp_pures.
      iApply ("IH" with "HΨ Htok").
    - iIntros (v') "Hv'". wp_pures. by iModIntro.
  Admitted.


  Import melocoton.ml_lang.logrel.logrel melocoton.ml_lang.logrel.fundamental.

  Lemma sem_typed_knot P Γ τ1 τ2 :
    ⊢ log_typed (p:=ML_knot_env) P Γ knot_code
      (* ((τ1 -> τ2) -> (τ1 -> τ2)) -> (τ1 -> τ2) *)
      (TArrow (TArrow (TArrow τ1 τ2) (TArrow τ1 τ2)) (TArrow τ1 τ2)).
  Proof.
    iIntros "!>" (Δ vs) "HΔ Hvs".
    iIntros "?". simpl. wp_pures. iModIntro. iFrame. iModIntro. iIntros (?) "#Hv".
    iIntros "Htok".
    iApply (wp_wand (val:=val)). { iApply knot_code_spec. }
    iIntros (rc) "#Hwp". iFrame. iIntros "!>" (v'') "#Ht1 Htok".
    iApply (wp_wand (val:=val) with "[Htok] []").
    1: iApply ("Hwp" $! ((⟦ τ2 ⟧ ML_knot_env) Δ) ((⟦ τ1 ⟧ ML_knot_env) Δ) with "[] [//] Htok").
    2: { iIntros (?) "[$ $]". }
    iIntros "!>" (rec) "#Hx".
    iIntros (v''') "#Hv''' Htok".
    wp_bind (App v _).
    iApply (wp_wand (val:=val) with "[Htok] []").
    { iApply "Hv"; [|done]. iIntros "!>" (?) "#? Htok".
      iApply (wp_wand (val:=val) with "[Htok] []").
      { by iApply "Hx". }
      iIntros (?) "[$ $]".
    }
    iIntros (?) "[#Hwp' Htok]".
    iApply (wp_wand (val:=val) with "[Htok] []").
    { by iApply ("Hwp'"). }
    iIntros (?) "[$ $]".
  Qed.

End ML_code.
