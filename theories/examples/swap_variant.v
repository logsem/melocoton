From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From iris.prelude Require Import options.
From melocoton Require Import named_props.
From melocoton.ml_lang.logrel Require logrel typing fundamental.
From melocoton.interop Require Import basics basics_resources.
From melocoton.lang_to_mlang Require Import lang weakestpre.
From melocoton.interop Require Import lang weakestpre update_laws wp_utils wp_ext_call_laws wp_simulation.
From melocoton.c_interop Require Import rules.
From melocoton.ml_lang Require Import notation lang_instantiation.
From melocoton.c_lang Require Import mlang_instantiation lang_instantiation.
From melocoton.ml_lang Require proofmode.
From melocoton.c_lang Require notation proofmode.
From melocoton.mlanguage Require Import progenv.
From melocoton.mlanguage Require weakestpre.
From melocoton.linking Require Import lang weakestpre.
From melocoton.combined Require Import adequacy rules.


Section C_prog.

Import
  melocoton.c_lang.notation
  melocoton.c_lang.proofmode
  melocoton.c_interop.notation.

Context `{SI:indexT}.
Context `{!ffiG Σ}.

Definition swap_variant_code (x : expr) : expr :=
  let: "v" := malloc (#1) in
  "v" <- Field("x", #0) ;;
  (call: &"registerroot" with ("v")) ;;
  let: "t" := (call: &"read_tag" with (x)) in
  let: "r" := caml_alloc(#1, !"t") in                          (* !t := not t *)
  Store_field("r", #0, *("v" +ₗ #0)) ;;
  CAMLreturn: "r" unregistering ["v"].

Definition swap_variant_func : function := Fun [BNamed "x"] (swap_variant_code "x").
Definition swap_variant_prog : lang_prog C_lang := {[ "swap_variant" := swap_variant_func ]}.

Definition swap_sum v :=
  match v with
  | InjLV v => Some (InjRV v)
  | InjRV v => Some (InjLV v)
  | _       => None
  end.

Definition swap_tag v :=
  match v with
  | TagDefault => TagInjRV
  | TagInjRV => TagDefault
  end.

Definition get_tag v :=
  match v with
  | InjLV _ => Some TagDefault
  | InjRV _ => Some TagInjRV
  | _       => None
  end.

Definition get_value v :=
  match v with
  | InjLV v | InjRV v => Some v
  | _ => None
  end.

Definition swap_variant_ml_spec : protocol ML_lang.val Σ :=
  !! (v: MLval) r
      {{ ⌜swap_sum v = Some r⌝ }}
        "swap_variant" with [ v ]
      {{ RETV r; True }}.

Lemma swap_variant_correct :
  prims_proto swap_variant_ml_spec ||- swap_variant_prog :: wrap_proto swap_variant_ml_spec.
Proof.
  iIntros (fn ws Φ) "H". iNamed "H". iNamedProto "Hproto".
  iSplit; first done. iIntros (Φ'') "HΦ".
  iAssert (⌜length lvs = 1⌝)%I as %Hlen.
  { by iDestruct (big_sepL2_length with "Hsim") as %?. }
  destruct lvs as [|lv []]; try by (exfalso; eauto with lia); []. clear Hlen.
  destruct ws as [|w []]; try by (exfalso; apply Forall2_length in Hrepr; eauto with lia); [].
  apply Forall2_cons_1 in Hrepr as [Hrepr _].
  cbn. iDestruct "Hsim" as "(Hsim&_)".
  wp_call_direct.

  wp_alloc rr as "H"; first done.
  change (Z.to_nat 1) with 1. cbn. iDestruct "H" as "(H&_)". rewrite loc_add_0.
  wp_pures.

  iAssert (∃ γ lvs vs tag, γ ↦imm (tag, [lvs]) ∗
                          lvs ~~ vs ∗
                          ⌜get_value v = Some vs⌝ ∗
                          ⌜get_tag v = Some tag⌝ ∗
                          ⌜repr_lval θ (Lloc γ) w⌝)%I as "#Hsim'".
  { destruct v; iDestruct "ProtoPre" as "%Hptsum"; try done; simplify_eq;
    iDestruct "Hsim" as (γ lvs ->) "[Hptsum Hrepr]"; fold block_sim.
    - iExists γ, lvs, v, TagDefault. repeat (iSplit; try done).
    - iExists γ, lvs, v, TagInjRV. repeat (iSplit; try done). }
  clear. iClear "Hsim".
  iDestruct "Hsim'" as (γ lvs vs tag) "(Hptsum&Hrepr&%Hvalue&%Htag&%Hrepr')".

  (* readfield *)
  wp_apply (wp_readfield with "[$HGC $Hptsum]"); try done.
  iIntros (v' wlv) "(HGC & _ & %Heq & %Hreprwlv)".
  change (Z.to_nat 0) with 0 in Heq. cbn in *. symmetry in Heq. simplify_eq.
  wp_apply (wp_store with "H"). iIntros "H". wp_pures.

  (* registerroot *)
  wp_apply (wp_registerroot with "[$HGC $H]"); [done..|].
  iIntros "(HGC & Hrr)". wp_pures.

  (* read_tag(w) *)
  wp_apply (wp_read_tag with "[$HGC ]"); [done..| |].
  { by iDestruct "Hptsum" as "[??]". }
  iIntros "[HGC _]". wp_pures.

  wp_bind (!_)%CE.
  iApply (wp_wand _ _ _ (λ v, ⌜v = OVal #C(vblock_tag_as_int (swap_tag tag))⌝)%I).
  { by destruct tag; wp_pures; done. }
  iIntros (v1 ->).

  (* alloc(!"t", #1) *)
  wp_apply (wp_alloc (swap_tag tag) with "HGC"); try done.
  iIntros (θ' γnew wnew) "(HGC & Hnew & %Hreprnew)". wp_pures.

  (* load from root *)
  wp_apply (load_from_root with "[HGC Hrr]"); rewrite loc_add_0; first iFrame.
  iIntros (wlv') "(Hr&HGC&%Hreprwlv')".

  (* modify *)
  wp_apply (wp_modify with "[$HGC $Hnew]"); [done..|].
  iIntros "(HGC & Hnew)". change (Z.to_nat 0) with 0. cbn.
  wp_pures.

  (* unregisterroot *)
  wp_apply (wp_unregisterroot with "[$HGC $Hr]"); [done..|].
  iIntros (wlv'') "(HGC & H & %Hrepr'')".
  repr_lval_inj. wp_pures.

  (* free *)
  iAssert (rr ↦C wlv')%I with "[H]" as "Hrr"; first done.
  wp_apply (wp_free with "Hrr"). iIntros "_".
  wp_pures.

  (* Finish, convert the new points-to to an immutable pointsto *)
  iMod (freeze_to_immut γnew _ θ' with "[$]") as "(HGC&#Hnew)".
  change (Z.to_nat 1) with 1; cbn.

  iModIntro. iApply "HΦ".
  iApply ("Return" $! _ _ (OVal (Lloc γnew)) with "HGC [Cont] [ProtoPre]").
  - by iApply "Cont".
  - destruct v; iDestruct "ProtoPre" as "%Hptpair"; try done;
    cbn in *; simplify_eq;
    cbn; iExists γnew, lvs; repeat (iSplit; try done).
  - iPureIntro. now constructor.
Qed.

End C_prog.

Section JustML.
Context `{SI:indexT}.
Context `{!ffiG Σ}.
Import melocoton.ml_lang.proofmode.

  Section LogRel.
  Import logrel typing fundamental.
  Context `{!logrelG Σ}.
  Context (A B : type).

  Definition program_type_ctx : program_env := 
    {[ "swap_variant" := FunType [ TSum A B ] (TSum B A) ]}.

  Lemma swap_variant_well_typed Δ : ⊢ ⟦ program_type_ctx ⟧ₚ* ⟨∅, swap_variant_ml_spec⟩ Δ.
  Proof.
    (* simplify_map_eq. *)
    iIntros (s vv Φ) "!> (%ats&%rt&%Heq&Hargs&Htok&HCont)".
    wp_extern. iModIntro. unfold program_type_ctx in Heq. simplify_map_eq.
    iPoseProof (big_sepL2_length with "Hargs") as "%Heq".
    destruct vv as [|v [|??]]; cbn in Heq; try lia.
    cbn. iDestruct "Hargs" as "([(%w&%Hv&Hargs)|(%w&%Hv&Hargs)]&_)".
    - rewrite Hv. iSplit; first done. iExists _, _.
      do 2 (iSplit; first done). iIntros "!> _".
      wp_pures. iModIntro. iApply ("HCont" with "[-Htok] Htok").
      iRight. iExists _. iSplit; first done. iFrame.
    - rewrite Hv. iSplit; first done. iExists _, _.
      do 2 (iSplit; first done). iIntros "!> _".
      wp_pures. iModIntro. iApply ("HCont" with "[-Htok] Htok").
      iLeft. iExists _. iSplit; first done. iFrame.
  Qed.

  End LogRel.

Definition crash := #() #().

Definition swap_variant_client : mlanguage.expr (lang_to_mlang ML_lang) :=
  (Match (Extern "swap_variant" [ (InjL #1)%MLE ]) "_" (crash) "x" (Var "x")).

Lemma ML_prog_correct_axiomatic :
  ⊢ WP swap_variant_client at ⟨∅, swap_variant_ml_spec⟩
    {{ v, ⌜∃x : Z, v = OVal #x ∧ x = 1⌝ }}.
Proof.
  unfold swap_variant_client. wp_pures.
  wp_extern.
  iModIntro. cbn. iSplit; first done. do 2 iExists _.
  do 2 (iSplitR; first done). iIntros "!> _".
  wp_pures. iModIntro. iPureIntro. by eexists.
Qed.

End JustML.

Local Existing Instance ordinals.ordI.

Definition fullprog : mlang_prog combined_lang :=
  combined_prog swap_variant_client swap_variant_prog.

Lemma swap_variant_adequate :
  umrel.trace (mlanguage.prim_step fullprog) (LkCall "main" [], adequacy.σ_init)
    (λ '(e, σ), mlanguage.to_outcome e = Some (OVal (code_int 1))).
Proof.
  eapply umrel_upclosed.
  { eapply combined_adequacy_trace. intros Σ Hffi. split_and!.
    3: {iIntros "_". iApply ML_prog_correct_axiomatic. }
    3: apply swap_variant_correct.
    { iIntros (? Hn ?) "(% & H)". iNamedProto "H".
      exfalso. set_solver. }
    { set_solver. } }
  { intros [?] (? & -> & ?). do 3 f_equal; done. }
Qed.

