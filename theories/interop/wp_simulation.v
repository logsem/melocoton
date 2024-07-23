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
From melocoton.ml_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.interop Require Export prims weakestpre prims_proto hybrid_ghost_heap.
From melocoton.interop Require Import wp_ext_call_laws wp_boundary_laws wp_utils.
From melocoton.interop.wp_prims Require Import common.
Import Wrap.

Section Simulation.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.

Implicit Types P : iProp Σ.
Import mlanguage.

Lemma wp_to_outcome (pe : progenv.prog_environ wrap_lang Σ) (o : outcome MLval):
  not_at_boundary
 -∗ WP (WrSE (ExprML (language.of_outcome ML_lang o))) at pe {{ ret,
   ∃ θ' fc' olv,
      GC θ'
    ∗ current_fc fc'
    ∗ ⌜repr_lval_out θ' olv ret⌝
    ∗ olv ~~ₒ o
    ∗ at_boundary wrap_lang }}.
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
    e' = WrSE (ExprO (ow)) ∧ σ' = CState ρc mem).
  iSplit.
  { iPureIntro. eapply OutS; try naive_solver.
    apply language.to_of_outcome. }

  iIntros (? ? (w & ρc & mem & Hout & Hcore & -> & ->)).
  iMod (wrap_interp_ml_to_c_out with "SI Hnb") as "(SI & Hb & HGC & H)";
    first done; first done.
  do 3 iModIntro. iFrame "SI".
  iApply weakestpre.wp_outcome'.
  iDestruct "H" as "((% & Hfc) & (% & Hls & %Hval))".
  repeat iExists _. iFrame. repeat iSplit; eauto.
Qed.

Lemma wp_simulates (Ψ : protocol ML_lang.val Σ) eml emain Φ :
  Ψ on prim_names ⊑ ⊥ →
  not_at_boundary -∗
  WP eml at ⟨ ∅, Ψ ⟩ {{ Φ }} -∗
  WP (WrSE (ExprML eml)) at ⟪ wrap_prog emain, wrap_proto Ψ ⟫ {{ o,
    ∃ θ' fc' ov olv,
      GC θ'
    ∗ current_fc fc'
    ∗ ⌜repr_lval_out θ' olv o⌝
    ∗ olv ~~ₒ ov
    ∗ Φ ov
    ∗ at_boundary wrap_lang }}.
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
    iPoseProof (wp_to_outcome _ o with "Hnb") as "Hwp".
    iDestruct (weakestpre.wp_strong_mono_post with "[Hret] Hwp") as "Hwp";
      last first.
    { rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
      iApply ("Hwp" $! (MLState ρml σ)). iFrame.
      iExists _. iFrame.
      iSplitR ""; last done.
      repeat iExists _. by iFrame. }
    { cbn. iIntros (vv) "(%θ' & %fc' & %olv & HGC & Hfc & %Hrep & Hval & ?)".
      repeat iExists _. by iFrame. }
  (* extcall *)
  + iDestruct "HWP" as "(%fn_name & %vs & %K' & -> & %Hfn & >(%Ξ & Hσ & HT & Hr))".
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
      e' = WrE (Wrap.ExprCall fn_name ws) [K'] ∧
      σ' = CState ρc mem).
    iSplit.
    { iPureIntro.
      eapply MakeCallS; eauto.
      { done. }
      { apply not_elem_of_dom. rewrite dom_wrap_prog not_elem_of_prim_names //. }
      { split_and!; eauto. }
      { intros * Hep (lvs & ? & ?). do 4 eexists. split_and!; eauto. } }
    iIntros (? ? (ws & ρc & mem & lvs & ? & ? & Hcore & -> & ->)).
    iMod (wrap_interp_ml_to_c with "[- Hnb Hr HT] Hnb") as "(Hσ & Hb & HGC & Hfc & (%lv & #Hblk & %))";
      first done.
    { exists lvs; split_and; eauto.  }
    { rewrite /wrap_state_interp /ML_state_interp /named.
      iSplitL "Hσ"; first by iFrame. iFrame. iExists fc.
      iSplitR "Hfc"; last by iFrame.
      repeat iExists _.
      by iFrame. }
    do 3 iModIntro. iFrame "Hσ".

    (* step done; make an external call in the wrapper *)

    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iIntros (st') "Hst'".
    iDestruct (SI_at_boundary_is_in_C with "Hst' Hb") as %(ρc'&mem'&->).

    iModIntro. iRight; iLeft. iExists fn_name, ws, [K'].
    iSplit; first done.
    iSplit.
    { iPureIntro. apply not_elem_of_dom.
      rewrite dom_wrap_prog not_elem_of_prim_names //. }
    iFrame "Hb Hst'".
    iExists (λ o, ∃ θ' fc' wret vret lvret,
        ⌜o = wret⌝
      ∗ GC θ'
      ∗ current_fc fc'
      ∗ Ξ vret
      ∗ lvret ~~ₒ vret
      ∗ ⌜repr_lval_out θ' lvret wret⌝)%I.
    iSplitL "HGC Hfc HT".
    { rewrite /wrap_proto /named /=.
      iDestruct "Hfc" as "(%fc' & Hfc)".
      repeat iExists _.
      iFrame "HGC Hfc HT Hblk". iSplit; first done.
      iIntros (? ? ? ?) "? ? ? ? %". repeat iExists _. iFrame. iPureIntro. eauto. }
    iNext.
    iIntros (o) "((%θ' & %fc' & %wret & %vret & %lvret & -> & HGC & Hfc & HΞ & Hsim & %) & Hb)".

    (* extcall done; take an administrative step for the call return *)

    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iIntros (st') "Hst' !>". clear dependent ρc' mem'.
    iDestruct (SI_at_boundary_is_in_C with "Hst' Hb") as %(ρc'&mem'&->). simpl.
    iRight; iRight. iSplit; first done.

    iDestruct ((wrap_interp_c_to_ml_out wret _ _ _ _ vret lvret) with "Hst' HGC Hfc Hb [Hsim]")
      as (ρml' σ' ζ Hc_to_ml_heap Hc_to_ml_out) "HH"; eauto.
    iExists (λ '(e2, σ2),
      e2 = WrSE (ExprML (language.fill K' (lang.ML_lang.of_outcome vret))) ∧
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
      e2 = WrSE (ExprML eml') ∧ σ2 = MLState ρml σ').
    iSplit.
    { iPureIntro. eapply StepMLS; eauto.
      by eapply reducible_not_val. }
    iIntros (? ? (e' & σ' & Hstep & -> & ->)).
    iMod ("HWP" $! _ _ Hstep) as "HWP".
    do 2 iModIntro. iMod "HWP" as "(HσC & HWP')".
    iModIntro. iSplitR "HWP' Hnb".
    { rewrite /weakestpre.state_interp /= /named.
      iSplitL "HσC"; iFrame. repeat iExists _.
      iSplitR "Hfc"; last by iFrame.
      repeat iExists _. by iFrame. }
    iApply ("IH" with "Hnb HWP'").
Qed.

Lemma callback_correct emain Ψ :
  Ψ on prim_names ⊑ ⊥ →
  wrap_proto Ψ |- wrap_prog emain :: callback_proto Ψ.
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
  iDestruct (wrap_interp_c_to_ml [w;w'] _ _ _ _ [RecV f x e; v']
    with "Hst HGC Hfc Hb [Hclos Hsim']") as (ρml' σ' ζ Hc_to_ml_heap Hc_to_ml_vals) "HH".
  { repeat constructor; eauto. }
  { iApply big_sepL2_cons. iSplit.
    { cbn. iExists _. by iFrame "Hclos". }
    { iApply big_sepL2_cons; iFrame. by iApply big_sepL2_nil. } }

  iModIntro.
  iRight; iRight. iSplit; first done.
  iExists (λ '(e2, σ2),
    e2 = WrSE (ExprML (App (Val (RecV f x e)) (Val v'))) ∧
    σ2 = MLState ρml' σ').
  iSplit. { iPureIntro. eapply CallbackS; eauto. }
  iIntros (? ? (-> & ->)). iMod "HH" as "(Hst & Hnb)".
  do 3 iModIntro. iFrame "Hst".
  iApply (weakestpre.wp_wand with "[-Cont Hcont Hclos]").
  { by iApply (wp_simulates with "Hnb [WPcallback]"). }
  cbn. iIntros (o) "(%θ' & %fc' & %lv & %vret & HGC & Hfc & % & Hsim & Hψ & ?)".
  iApply "Hcont". iFrame.
  iApply "Cont". iFrame; eauto.
Qed.

Lemma main_correct emain Ψ P (Φ : Z → Prop) :
  Ψ on prim_names ⊑ ⊥ →
  (⊢ P -∗ WP emain at ⟨∅, Ψ⟩ {{ k, ⌜∃ x, k = OVal (LitV (LitInt x)) ∧ Φ x⌝ }}) →
  wrap_proto Ψ |- wrap_prog emain :: main_proto Φ P.
Proof using.
Admitted.
(*   iIntros (Hnprim Hmain ? ? ?) "Hproto". iNamedProto "Hproto". *)
(*   iSplit; first done. iIntros (Φ') "Hb Hcont". *)
(*   iApply wp_wrap_call; first done. cbn [snd]. *)
(*   rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre. *)
(*   iIntros (st) "Hst". *)
(*   iDestruct (SI_at_boundary_is_in_C with "Hst Hb") as %(ρc&mem&->). simpl. *)
(*   iNamed "Hst". iNamed "SIC". unfold gctoken.at_init. *)
(*   iDestruct (ghost_var_agree with "Hat_init SIinit") as %?; simplify_eq. *)
(*   iNamed "Hinit". iRename "Hat_init" into "GCinit". *)
(*   destruct ρc. cbn [state.ζC state.χC state.θC state.rootsC] in *. SI_GC_agree. *)
(*   iAssert (ghost_var wrapperG_γat_init 1 true) with "[GCinit SIinit]" as "SIinit". *)
(*   { rewrite -{3}Qp.half_half. *)
(*     iApply (fractional.fractional_merge _ _ (λ q, ghost_var wrapperG_γat_init q true) *)
(*              with "GCinit SIinit"). } *)
(*   iMod (ghost_var_update false with "SIinit") as "SIinit". *)
(*   iMod (ghost_var_update_halves false with "Hb SIbound") as "[Hb SIbound]". *)
(**)
(*   iModIntro. *)
(*   iRight; iRight. iSplit; first done. *)
(*   iExists (λ '(e2, σ2), *)
(*     e2 = WrSE (ExprML emain) ∧ *)
(*     σ2 = MLState {| χML := ∅; ζML := ∅; rootsML := ∅ |} ∅). *)
(*   iSplit. { iPureIntro. eapply MainS; eauto. } *)
(*   iIntros (? ? (-> & ->)). *)
(*   do 3 iModIntro. *)
(**)
(*   rewrite [X in ghost_var wrapperG_γat_init X _](_: 1 = 1/2 + 1/2)%Qp; *)
(*     last by rewrite Qp.half_half. *)
(*   iDestruct (ghost_var_split _ _ (1/2) (1/2) with "SIinit") as "[Hinit1 Hinit2]". *)
(*   rewrite /weakestpre.state_interp /= /named. *)
(*   rewrite /ML_state_interp /= /named. *)
(*   rewrite /public_state_interp. *)
(*   rewrite !fmap_empty !right_id_L !dom_empty_L. iFrame. *)
(*   (* rewrite /named !dom_empty_L big_sepS_empty. iFrame. *) *)
(*   iSplitL "GCζvirt GCχvirt GCrootsm". *)
(*     { iExists []. iSplit. eauto. iApply (hgh_empty with "[$] [$]"). } *)
(**)
(*   iApply (weakestpre.wp_wand with "[-Cont Hcont]"). *)
(*   { iApply (wp_simulates with "Hb [Hinitial_resources]"); first done. *)
(*     iApply (Hmain with "[$]"). } *)
(*   cbn. iIntros (o) "(%θ' & %v & %lv & HGC & %Hrepr & Hsim & HΦ' & ?)". *)
(*   iDestruct "HΦ'" as (?) "[%Hv %HΦ]". inversion Hv. subst. *)
(*   destruct lv. *)
(*   { iDestruct "Hsim" as "->". inversion Hrepr; simplify_eq. *)
(*     inversion H2; simplify_eq. *)
(*     iApply "Hcont". iFrame. by iApply "Cont". } *)
(* Qed. *)

Lemma wrap_correct emain Ψ (Φ : Z → Prop) P :
  Ψ on prim_names ⊑ ⊥ →
  (⊢ P -∗ WP emain at ⟨∅, Ψ⟩ {{ k, ⌜∃ x, k = OVal (LitV (LitInt x)) ∧ Φ x⌝ }}) →
  wrap_proto Ψ |- wrap_prog emain :: prims_proto Ψ ⊔ main_proto Φ P.
Proof using.
  intros Hnprim Hmain.
  iIntros (? ? ?) "[Hprim|Hmain]".
  { iDestruct "Hprim" as (p) "H".
    destruct p; last (by iExFalso); try by iApply (base_prim_correct with "H").
    by iApply (callback_correct with "H"). }
  { by iApply (main_correct with "Hmain"). }
Qed.

End Simulation.
