From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import state lang basics_resources.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Import defs resources.
From melocoton.ml_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.interop Require Export prims weakestpre prims_proto.
From melocoton.interop Require Import wp_ext_call_laws wp_boundary_laws wp_utils.
Import Wrap.

Section Simulation.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Implicit Types P : iProp Σ.
Import mlanguage.

Lemma wp_to_val (pe : weakestpre.prog_environ wrap_lang Σ) E v:
    not_at_boundary
 -∗ WP (WrSE (ExprML (ML_lang.Val v))) @ pe; E {{ w,
      ∃ θ' lv, GC θ' ∗ ⌜repr_lval θ' lv w⌝ ∗ lv ~~ v ∗
      at_boundary wrap_lang }}.
Proof using.
  iIntros "Hnb".
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%st SI".
  iDestruct (SI_not_at_boundary_is_in_ML with "SI Hnb") as "%H"; destruct H as (ρml & σ & ->).
  iModIntro. iRight. iRight.
  iSplit; first done.

  iAssert (⌜ml_to_c [v] ρml σ (λ ws ρc mem, ml_to_c_core [v] ρml σ ws ρc mem)⌝)%I as "%Hprog".
  { iNamed "SI". iNamed "SIML".
    iDestruct (interp_ML_discarded_locs_pub with "HσML SIAχNone") as "%H". iPureIntro.
    split_and!; eauto. }

  iExists (λ '(e', σ'), ∃ w ρc mem,
    ml_to_c_core [v] ρml σ [w] ρc mem ∧
    e' = WrSE (ExprV w) ∧ σ' = CState ρc mem).
  iSplit. { iPureIntro. eapply ValS; naive_solver. }

  iIntros (? ? (w & ρc & mem & Hcore & -> & ->)).
  iMod (wrap_interp_ml_to_c with "SI Hnb") as "(SI & Hb & HGC & (%lvs & Hsim & %Hrepr))";
    first done.
  do 3 iModIntro. iFrame "SI". iApply weakestpre.wp_value'.
  iDestruct (big_sepL2_cons_inv_l with "Hsim") as "(% & % & -> & Hsim & _)".
  iExists _, _. iFrame. by inversion Hrepr; simplify_eq.
Qed.

Lemma wp_simulates (pe : prog_environ ML_lang Σ) E eml Φ :
  penv_prog pe = ∅ → (* XXX *)
     not_at_boundary
  -∗ (∀ fn_name vs Φ, ⌜is_prim_name fn_name⌝ -∗ penv_proto pe fn_name vs Φ -∗ False)
  -∗ WP eml @ pe; E {{ Φ }}
  -∗ WP (WrSE (ExprML eml)) @ (wrap_penv pe); E {{ w,
       ∃ θ' lv v, GC θ' ∗ ⌜repr_lval θ' lv w⌝ ∗ lv ~~ v ∗ Φ v ∗
       at_boundary wrap_lang }}.
Proof using.
  intros Hpeemp.
  iLöb as "IH" forall (eml).
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  rewrite wp_unfold. rewrite /wp_pre.
  iIntros "Hnb Hnprim HWP %st Hst".
  iDestruct (SI_not_at_boundary_is_in_ML with "Hst Hnb") as %(ρml&σ&->).
  iNamed "Hst". iNamed "SIML".
  iDestruct (interp_ML_discarded_locs_pub with "HσML SIAχNone") as %Hpublocs.
  iMod ("HWP" $! σ with "[$HσML $HσMLdom]") as "[HWP|[HWP|HWP]]".
  (* value *)
  + iDestruct "HWP" as "(%x & -> & Hσ & Hret)".
    iPoseProof (wp_to_val (wrap_penv pe) E x with "Hnb") as "Hwp".
    iDestruct (weakestpre.wp_strong_mono_post with "[Hret] Hwp") as "Hwp";
      last first.
    { rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
      iApply ("Hwp" $! (MLState ρml σ)). iFrame. by iPureIntro. }
    { cbn. iIntros (v) "(%θ' & %lv & ? & ? & ? & ?)". iExists _, _, _. iFrame. }
  (* extcall *)
  + iDestruct "HWP" as "(%fn_name & %vs & %K' & -> & %Hfn & >(%Ξ & Hσ & HT & Hr))".
    iAssert (⌜¬ is_prim_name fn_name⌝)%I with "[Hnprim HT]" as "%Hnprim".
    { destruct (decide (is_prim_name fn_name)) as [His|]; last by eauto.
      iExFalso. iApply "Hnprim"; eauto. }

    (* take an administrative step in the wrapper *)

    iModIntro. iRight; iRight.
    iSplit; first done.
    iExists (λ '(e', σ'), ∃ ws ρc mem,
      ml_to_c_core vs ρml σ ws ρc mem ∧
      e' = WrE (Wrap.ExprCall fn_name ws) [K'] ∧
      σ' = CState ρc mem).
    iSplit.
    { iPureIntro.
      eapply MakeCallS with (YC := (λ ws ρc mem, ml_to_c_core vs ρml σ ws ρc mem)); eauto.
      { done. }
      { rewrite /wrap_penv /= lookup_prims_prog_None //. }
      { split_and!; eauto. }
      { naive_solver. } }
    iIntros (? ? (ws & ρc & mem & Hcore & -> & ->)).
    iMod (wrap_interp_ml_to_c with "[- Hnb Hnprim Hr HT] Hnb") as "(Hσ & Hb & HGC & (%lvs & #Hblk & %))";
      first done.
    { rewrite /wrap_state_interp /ML_state_interp /named.
      iSplitL "Hσ"; first by iFrame. by iFrame. }
    do 3 iModIntro. iFrame "Hσ".

    (* step done; make an external call in the wrapper *)

    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iIntros (st') "Hst'".
    iDestruct (SI_at_boundary_is_in_C with "Hst' Hb") as %(ρc'&mem'&->).

    iModIntro. iRight; iLeft. iExists fn_name, ws, [K'].
    iSplit; first done.
    iSplit; first rewrite /wrap_penv /= lookup_prims_prog_None //.
    iFrame "Hb Hst'".
    iExists (λ wret, ∃ θ' vret lvret, GC θ' ∗ Ξ vret ∗ lvret ~~ vret ∗ ⌜repr_lval θ' lvret wret⌝)%I.
    iSplitL "HGC HT".
    { rewrite {2}/wrap_penv /wrap_proto /named /=. iExists _, _, _, _.
      iFrame "HGC HT Hblk". iSplit; first done.
      iIntros (? ? ? ?) "? ? ? %". iExists _, _, _. by iFrame. }
    iNext. iIntros (wret) "((%θ' & %vret & %lvret & HGC & HΞ & Hsim & %) & Hb)".

    (* extcall done; take an administrative step for the call return *)

    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iIntros (st') "Hst' !>". clear dependent ρc' mem'.
    iDestruct (SI_at_boundary_is_in_C with "Hst' Hb") as %(ρc'&mem'&->). simpl.
    iRight; iRight. iSplit; first done.

    iDestruct (wrap_interp_c_to_ml with "Hst' HGC Hb Hsim") as (ρml' σ' Hc_to_ml) "HH";
      first done.
    iExists (λ '(e2, σ2),
      e2 = WrSE (ExprML (language.fill K' (Val vret))) ∧
      σ2 = MLState ρml' σ').
    iSplit. { iPureIntro. eapply RetS; eauto. }
    iIntros (? ? (-> & ->)). iMod "HH" as "[Hst' Hnb]".
    do 3 iModIntro. iFrame "Hst'".

    (* continue execution using IH *)

    iApply ("IH" with "Hnb Hnprim"). by iApply "Hr".

  (* step *)
  + iDestruct "HWP" as "(%Hred & HWP)".
    iModIntro. iRight. iRight. iSplit; first done.
    iExists (λ '(e2, σ2), ∃ eml' σ',
      language.language.prim_step ∅ eml σ eml' σ' ∧
      e2 = WrSE (ExprML eml') ∧ σ2 = MLState ρml σ').
    iSplit.
    { iPureIntro. eapply StepMLS; eauto.
      { by eapply reducible_not_val. }
      { by rewrite Hpeemp in Hred. } }
    iIntros (? ? (e' & σ' & Hstep & -> & ->)).
    rewrite Hpeemp. iMod ("HWP" $! _ _ Hstep) as "HWP".
    do 2 iModIntro. iMod "HWP" as "(HσC & HWP')".
    iModIntro. iSplitR "HWP' Hnb Hnprim".
    { rewrite /weakestpre.state_interp /= /named.
      iSplitL "HσC"; by iFrame. }
    iApply ("IH" with "Hnb Hnprim HWP'").
Qed.

Lemma wp_base_primitives (pe : prog_environ ML_lang Σ) prim ws E Φ :
  penv_prog pe = ∅ → (* XXX *)
  (∀ fn_name vs Φ, ⌜is_prim_name fn_name⌝ -∗ penv_proto pe fn_name vs Φ -∗ False) -∗
  proto_prims E (penv_proto pe) prim ws Φ -∗
  at_boundary wrap_lang -∗
  WP (WrSE (RunPrimitive prim ws)) @ (wrap_penv pe); E {{ w,
    at_boundary wrap_lang ∗ Φ w }}.
Proof using.
  iIntros (Hpeemp) "Hnprims [Hproto|Hcallback] Hb".
  { (* base primitives *)
    iApply (wp_base_prims with "Hb Hproto").
    iIntros "!>" (?) "? ?". iApply weakestpre.wp_value; first done.
    iFrame. }
  { (* callbacks *)
    iNamed "Hcallback".

    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iIntros (st) "Hst".
    iDestruct (SI_at_boundary_is_in_C with "Hst Hb") as %(ρc&mem&->). simpl.
    iAssert (⌜θ = θC ρc ∧
              gmap_inj (θC ρc) ∧
              ζC ρc !! γ = Some (Bclosure f x e)⌝)%I
      as %(-> & Hθinj & Hγ).
    { iNamed "Hst". iNamed "HGC". iNamed "SIC". SI_GC_agree.
      iDestruct (lstore_own_immut_of with "[$] Hclos") as %(Hγvirt & _).
      iPureIntro. split; eauto. split; first by apply HGCOK.
      eapply freeze_lstore_lookup_bclosure; first done.
      eapply lookup_union_Some_r; eauto. }

    iModIntro.
    iRight; iRight. iSplit; first done.

    iDestruct (wrap_interp_c_to_ml with "Hst HGC Hb Hsim'") as (ρml' σ' Hc_to_ml) "HH";
      first done.
    iExists (λ '(e2, σ2),
      e2 = WrSE (ExprML (App (Val (RecV f x e)) (Val v'))) ∧
      σ2 = MLState ρml' σ').
    iSplit. { iPureIntro. eapply CallbackS; eauto. }
    iIntros (? ? (-> & ->)). iMod "HH" as "(Hst & Hnb)".
    do 3 iModIntro. iFrame "Hst".

    iApply (weakestpre.wp_wand with "[-Cont Hclos]").
    { iApply (wp_simulates with "Hnb Hnprims [WPcallback]"); try done.
      destruct pe; cbn in Hpeemp |- *. rewrite Hpeemp. iApply "WPcallback". }
    cbn. iIntros (v) "(%θ' & %lv & %vret & HGC & % & Hsim & Hψ & $)".
    iApply ("Cont" with "[$] [$] [$]"); eauto. }
Qed.

End Simulation.
