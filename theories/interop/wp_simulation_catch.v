From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import state lang basics_resources.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Import defs resources.
From melocoton.ml_lang Require Import lang lang_instantiation primitive_laws proofmode.
From melocoton.interop Require Export prims weakestpre prims_proto hybrid_ghost_heap.
From melocoton.interop Require Import wp_ext_call_laws wp_boundary_laws wp_utils.
From melocoton.interop.wp_prims Require Import common.
Import Wrap.

Section Simulation_catch.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.

Implicit Types P : iProp Σ.
Import mlanguage.

Local Notation CValI n := (C_intf.LitV (C_intf.LitInt n)).
Local Notation CValL a := (C_intf.LitV (C_intf.LitLoc a)).
Local Notation HVal v := (Some (Some v)).

Lemma wp_to_outcome_catch (pe : progenv.prog_environ wrap_lang Σ) (o : outcome MLval):
  not_at_boundary
 -∗ WP (WrSE (ExprML (language.of_outcome ML_lang o) true)) at pe {{ ret,
   ∃ θ' exn lv a w,
     ⌜ret = OVal (CValL a)⌝ ∗
     a ↦C∗ [exn; w] ∗
     GC θ' ∗
     match o with
     | OVal v => ⌜exn = CValI 0⌝ ∗ ⌜repr_lval θ' lv w⌝ ∗ lv ~~ v
     | OExn v => ⌜exn = CValI 1⌝ ∗ ⌜repr_lval θ' lv w⌝ ∗ lv ~~ v
     end ∗
     at_boundary wrap_lang }}.
Proof using.
  iIntros "Hnb".
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%st SI".
  iDestruct (SI_not_at_boundary_is_in_ML with "SI Hnb") as "%H"; destruct H as (ρml & σ & ->).
  iModIntro. iRight. iRight.

  iSplit; first done.
  iAssert (⌜check_ml_state ρml σ⌝)%I as "%Hprog".
  { iNamed "SI". iNamed "SIML". iNamed "SIGCrem".
    iDestruct (hgh_discarded_locs_pub with "GCHGH HσML") as %?.
    iDestruct (hgh_dom_lstore_sub with "GCHGH") as %?.
    iDestruct (hgh_χ_inj with "GCHGH") as %?.
    iPureIntro; split_and!; eauto. }

  iExists (λ '(e', σ'), ∃ ow ρc mem,
    ml_to_c_heap ρml σ ρc mem ∧
    ml_to_c_outcome o ow ρc ∧
    e' = WrSE (ExprOC (ow)) ∧ σ' = CState ρc mem).
  iSplit.
  { iPureIntro. eapply OutS; try naive_solver.
    apply language.to_of_outcome. }

  iIntros (? ? (w & ρc & mem & Hout & Hcore & -> & ->)).
  iMod (wrap_interp_ml_to_c_out with "SI Hnb") as "(SI & Hb & HGC & H)";
    first done; first done.
  do 3 iModIntro. iFrame "SI".

  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%st SI".
  iDestruct (SI_at_boundary_is_in_C with "SI Hb") as "%H"; destruct H as (ρc' & σ' & ->).
  iModIntro. iRight. iRight.
  iSplit; first done.

  pose (match w with OVal _ => 0 | OExn _ => 1 end) as is_exn.
  pose (match w with OVal v | OExn v => v end) as ov.

  iExists (λ '(e'', σ''), ∃ a nmem,
    σ' !! a = None ∧
    σ' !! (a +ₗ 1) = None ∧
    nmem = heap_array a [HVal (CValI is_exn); HVal ov] ∪ σ' ∧
    e'' = WrSE (ExprO (OVal (CValL a))) ∧
    σ'' = CState ρc' (heap_array a [HVal (CValI is_exn); HVal ov] ∪ σ')).
  iSplit.
  { iPureIntro. eapply RetCS; intros. eexists a, _; split_and!; eauto.
    destruct w; subst; eauto. }

  iIntros (? ? (a & nmem' & Ha & Ha1 & -> & -> & ->)). do 2 iModIntro.
  iDestruct "SI" as "[HσC SIC]".
  iMod (gen_heap_alloc_big σ' (heap_array a [HVal (CValI is_exn); HVal ov]) with "[HσC]")
    as "(Hσ & Hl & Hm)"; eauto.
  { apply heap_array_map_disjoint; cbn. intros i Hi0 Hil.
    assert (i = 0 ∨ i = 1) as [-> | ->] by lia; eauto. now rewrite loc_add_0. }
  iModIntro. iFrame.

  iApply weakestpre.wp_outcome'.
  iDestruct "H" as "(%olv & Hls & %Hval)". cbn.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros H. rewrite lookup_union_r in H.
    { rewrite lookup_empty in H. congruence. }
    rewrite insert_empty. apply lookup_singleton_ne. destruct l'.
    inversion 1. lia. }
  iDestruct "Hl" as "[Ha1 Ha2]".
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some. intros [<- H'].
    rewrite lookup_empty. congruence. }
  iDestruct "Ha2" as "[Ha2 _]".
  destruct o; destruct olv; try iDestruct "Hls" as "%H";
  try (now inversion H);
  inversion Hval; subst;
  iExists _, _, _, _, _; iFrame; repeat (iSplit; eauto).
  all: iSplitR "Ha2"; try rewrite loc_add_0; rewrite big_opM_singleton; eauto.
Qed.

Lemma wp_simulates_catch (Ψ : protocol ML_lang.val Σ) eml emain Φ :
  Ψ on prim_names ⊑ ⊥ →
  not_at_boundary -∗
  WP eml at ⟨ ∅, Ψ ⟩ {{ Φ }} -∗
  WP (WrSE (ExprML eml true)) at ⟪ wrap_prog emain, wrap_proto Ψ ⟫
  {{ o, ∃ θ' res is_exn ret lret wret,
    ⌜o = OVal (C_intf.LitV (C_intf.LitLoc res))⌝ ∗
    GC θ' ∗
    res ↦C∗ [ C_intf.LitV (C_intf.LitInt is_exn); wret ] ∗
    lret ~~ ret ∗ ⌜repr_lval θ' lret wret⌝ ∗
    at_boundary wrap_lang ∗
    if Z.eqb is_exn 0%Z
    then Φ (OVal ret)
    else Φ (OExn ret) }}.
Proof.
  intros Hnprims.
  iLöb as "IH" forall (eml).
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  rewrite wp_unfold. rewrite /wp_pre.
  iIntros "Hnb HWP %st Hst".
  iDestruct (SI_not_at_boundary_is_in_ML with "Hst Hnb") as %(ρml&σ&->).
  iNamed "Hst". iNamed "SIML". iNamed "SIGCrem".
  iDestruct (hgh_discarded_locs_pub with "GCHGH HσML") as %Hpublocs.
  iMod ("HWP" $! σ with "[$HσML]") as "[HWP|[HWP|HWP]]".
  (* value *)
  + iDestruct "HWP" as "(%o & -> & Hσ & Hret)".
    iPoseProof (wp_to_outcome_catch _ o with "Hnb") as "Hwp".
    iDestruct (weakestpre.wp_strong_mono_post with "[Hret] Hwp") as "Hwp";
      last first.
    { rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
      iApply ("Hwp" $! (MLState ρml σ)). iFrame. by iPureIntro. }
    { iIntros (vv) "(%θ' & %exn & %lv & %a & %w & -> & Ha & HGC & H & ?)".
      destruct o; iExists θ', a, _, v, lv, w; iFrame;
      iDestruct "H" as "(-> & %Hr & Hb)"; iFrame; iSplit; eauto. }
  (* extcall *)
  + iDestruct "HWP" as "(%fn_name & %vs & %K' & %H & %Hfn & >(%Ξ & Hσ & HT & Hr))".
    iAssert (⌜¬ is_prim_name fn_name⌝)%I with "[HT]" as "%Hnprim".
    { destruct (decide (is_prim_name fn_name)) as [His|]; last by eauto.
      cbn -[wrap_prog]. iDestruct (Hnprims with "[HT]") as "%"; last done.
      rewrite /proto_on. iFrame. iPureIntro. by eapply elem_of_prim_names. }
    iDestruct (hgh_dom_lstore_sub with "GCHGH") as %?.
    iDestruct (hgh_χ_inj with "GCHGH") as %?.

    (* take an administrative step in the wrapper *)

    iModIntro. iRight; iRight.
    iSplit; first done.
    iExists (λ '(e', σ'), ∃ ws ρc mem lvs,
      Forall2 (is_val (χC ρc) (ζC ρc)) vs lvs ∧
      Forall2 (repr_lval (θC ρc)) lvs ws ∧
      ml_to_c_heap ρml σ ρc mem ∧
      e' = WrE (Wrap.ExprCall fn_name ws) [(K', true)] ∧
      σ' = CState ρc mem).
    iSplit.
    { iPureIntro.
      eapply MakeCallS; eauto.
      { apply not_elem_of_dom. rewrite dom_wrap_prog not_elem_of_prim_names //. }
      { split_and!; eauto. }
      { intros * Hep (lvs & ? & ?). do 4 eexists. split_and!; eauto. } }
    iIntros (? ? (ws & ρc & mem & lvs & ? & ? & Hcore & -> & ->)).
    iMod ((wrap_interp_ml_to_c vs lvs _ _ ws) with "[- Hnb Hr HT] Hnb")
      as "(Hσ & Hb & HGC & (#Hblk & %))"; eauto.
    { rewrite /wrap_state_interp /ML_state_interp /named.
      iSplitL "Hσ"; first by iFrame. by iFrame. }
    do 3 iModIntro. iFrame "Hσ".

    (* step done; make an external call in the wrapper *)

    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iIntros (st') "Hst'".
    iDestruct (SI_at_boundary_is_in_C with "Hst' Hb") as %(ρc'&mem'&->).

    iModIntro. iRight; iLeft. iExists fn_name, ws, [(K', true)].
    iSplit; first done.
    iSplit.
    { iPureIntro. apply not_elem_of_dom.
      rewrite dom_wrap_prog not_elem_of_prim_names //. }
    iFrame "Hb Hst'".
    iExists (λ o, ∃ θ' wret vret lvret, ⌜o = wret⌝ ∗ GC θ' ∗ Ξ vret ∗ lvret ~~ₒ vret ∗ ⌜repr_lval_out θ' lvret wret⌝)%I.
    iSplitL "HGC HT".
    { rewrite /wrap_proto /named /=. iExists _, _, _, _.
      iFrame "HGC HT Hblk". iSplit; first done.
      iIntros (? ? ? ?) "? ? ? %". iExists _, _, _, _. iFrame. iPureIntro. eauto. }
    iNext. iIntros (o) "((%θ' & %wret & %vret & %lvret & -> & HGC & HΞ & Hsim & %) & Hb)".

    (* extcall done; take an administrative step for the call return *)

    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iIntros (st') "Hst' !>". clear dependent ρc' mem'.
    iDestruct (SI_at_boundary_is_in_C with "Hst' Hb") as %(ρc'&mem'&->). simpl.
    iRight; iRight. iSplit; first done.

    iDestruct ((wrap_interp_c_to_ml_out wret _ _ _ vret lvret) with "Hst' HGC Hb [Hsim]")
      as (ρml' σ' ζ Hc_to_ml_heap Hc_to_ml_out) "HH"; eauto.
    iExists (λ '(e2, σ2),
      e2 = WrSE (ExprML (language.fill K' (lang.ML_lang.of_outcome vret)) true) ∧
      σ2 = MLState ρml' σ').
    iSplit. { iPureIntro. eapply RetS; eauto. }
    iIntros (? ? (-> & ->)). iMod "HH" as "[Hst' Hnb]".
    do 3 iModIntro. iFrame "Hst'".

    (* continue execution using IH *)
    iApply ("IH" with "Hnb").
    by iApply "Hr".

  (* step *)
  + iDestruct "HWP" as "(%Hred & HWP)".
    iModIntro. iRight. iRight. iSplit; first done.
    iExists (λ '(e2, σ2), ∃ eml' σ',
      language.language.prim_step ∅ eml σ eml' σ' ∧
      e2 = WrSE (ExprML eml' true) ∧ σ2 = MLState ρml σ').
    iSplit.
    { iPureIntro. eapply StepMLS; eauto.
      by eapply reducible_not_val. }
    iIntros (? ? (e' & σ' & Hstep & -> & ->)).
    iMod ("HWP" $! _ _ Hstep) as "HWP".
    do 2 iModIntro. iMod "HWP" as "(HσC & HWP')".
    iModIntro. iSplitR "HWP' Hnb".
    { rewrite /weakestpre.state_interp /= /named.
      iSplitL "HσC"; by iFrame. }
    iApply ("IH" with "Hnb HWP'").
Qed.

Lemma callback_exn_correct emain Ψ :
  Ψ on prim_names ⊑ ⊥ →
  wrap_proto Ψ |- wrap_prog emain :: callback_exn_proto Ψ.
Proof using.
  iIntros (Hnprim ? ? ?) "Hproto". iNamedProto "Hproto".
  iSplit; first done. iIntros (Φ'') "Hb Hcont".
  iApply wp_wrap_call; first done. cbn [snd].

  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros (st) "Hst".
  iDestruct (SI_at_boundary_is_in_C with "Hst Hb") as %(ρc&mem&->). simpl.
  iAssert (⌜θ = θC ρc ∧
            gmap_inj (θC ρc) ∧
            ζC ρc !! γ = Some (Bclosure f x e)⌝)%I
    as %(-> & Hθinj & Hγ).
  { iNamed "Hst". iNamed "HGC". iNamed "SIC". SI_GC_agree.
    iDestruct (hgh_lookup_block with "GCHGH [Hclos]") as %(?&Hfrz&?);
      first by iDestruct "Hclos" as "($&_)".
    inversion Hfrz; subst; eauto. }

  iDestruct "Hclos" as "#Hclos".
  iDestruct (wrap_interp_c_to_ml [w;w'] _ _ _ [RecV f x e; v']
    with "Hst HGC Hb [Hclos Hsim']") as (ρml' σ' ζ Hc_to_ml_heap Hc_to_ml_vals) "HH".
  { repeat constructor; eauto. }
  { iApply big_sepL2_cons. iSplit.
    { cbn. iExists _. by iFrame "Hclos". }
    { iApply big_sepL2_cons; iFrame. by iApply big_sepL2_nil. } }

  iModIntro.
  iRight; iRight. iSplit; first done.
  iExists (λ '(e2, σ2),
    e2 = WrSE (ExprML (App (Val (RecV f x e)) (Val v')) true) ∧
    σ2 = MLState ρml' σ').
  iSplit. { iPureIntro. eapply CallbackexnS; eauto. }
  iIntros (? ? (-> & ->)). iMod "HH" as "(Hst & Hnb)".
  do 3 iModIntro. iFrame "Hst".
  iApply (weakestpre.wp_wand with "[-Cont Hcont Hclos]").
  { iApply (wp_simulates_catch with "Hnb [WPcallback]"); eauto. }
  cbn. iIntros (o) "(%θ' & %res & %is_exn & %ret & %lret & %wret & -> & HGC & H)".
  iDestruct "H" as "((Hexn & Hres & _) & Hb & Hr & ? & H)".
  iApply "Hcont". iFrame.
  iApply "Cont". iFrame; eauto.
Qed.

End Simulation_catch.
