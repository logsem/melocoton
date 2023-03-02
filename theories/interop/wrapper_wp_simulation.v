From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem basics_resources wrapperstate.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.interop Require Import linking_wp basics prims wrapper_wp wrapper_wp_block_sim
  wrapper_wp_utils wrapper_wp_ext_call_laws wrapper_wp_boundary_laws.
Import Wrap.

Section Simulation.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Notation MLval := ML_lang.val.
Notation Cval := C_lang.val.

Implicit Types P : iProp Σ.
Import mlanguage.

Lemma wp_to_val (pe : weakestpre.prog_environ wrap_lang Σ) E v:
    not_at_boundary
 -∗ WP (WrSE (ExprML (ML_lang.Val v))) @ pe; E {{ w,
      ∃ θ' lv, GC θ' ∗ ⌜repr_lval θ' lv w⌝ ∗ block_sim v lv ∗
      at_boundary wrap_lang }}.
Proof.
  iIntros "Hnb".
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%st SI".
  iDestruct (SI_not_at_boundary_is_in_ML with "SI Hnb") as "%H"; destruct H as (ρml & σ & ->).
  iModIntro. iRight. iRight. iSplit.
  { iNamed "SI". iNamed "SIML".
    iDestruct (interp_ML_discarded_locs_pub with "HσML SIAχNone") as %Hpublocs.
    destruct (ml_to_c_exists [v] ρml σ) as (ws & ρc & mem & Hml_to_c); auto; [].
    iPureIntro. exists (λ _, True); eexists [], (WrE _ []); split. done.
    assert (Hlen: length ws = 1) by
      (erewrite <-(ml_to_c_words_length [v] _ _ ws); eauto).
    destruct ws as [| ? [|]]; try (cbn in Hlen; congruence).
    eapply ValS; eauto. }

  iIntros (X Hstep).
  destruct Hstep as ([] & [e1 k1] & Heq & Hstep).
  2: { exfalso. cbn in Heq. destruct k1; simplify_list_eq. }
  rewrite /= app_nil_r in Heq. simplify_eq.
  inversion Hstep; simplify_eq.
  { exfalso; apply language.language.val_stuck in H3; cbn in H3; done. }
  { exfalso.
    (* XXX fragile *)
    pose proof (@language.language.fill_not_val _ ML_lang k eml).
    rewrite /= H {2}/language.language.to_val /= in H0.
    enough (language.language.to_val eml = None) by naive_solver.
    rewrite /language.language.to_val H2 //. }

  cbn in * |-; simplify_eq.
  iMod (wrap_interp_ml_to_c with "SI Hnb") as "(SI & Hb & HGC & (%lvs & Hsim & %Hrepr))";
    first done.
  do 3 iModIntro. do 2 iExists _. iSplit; first done. iFrame "SI".
  iApply weakestpre.wp_value'.
  iDestruct (big_sepL2_cons_inv_l with "Hsim") as "(% & % & -> & Hsim & _)".
  iExists _, _. iFrame. by inversion Hrepr; simplify_eq.
Qed.


Lemma wp_simulates (pe : prog_environ ML_lang Σ) E eml Φ :
  penv_prog pe = ∅ → (* XXX *)
     not_at_boundary
  -∗ (∀ fn_name vs Φ, ⌜is_prim_name fn_name⌝ -∗ penv_proto pe fn_name vs Φ -∗ False)
  -∗ WP eml @ pe; E {{ Φ }}
  -∗ WP (WrSE (ExprML eml)) @ (wrap_penv pe); E {{ w,
       ∃ θ' lv v, GC θ' ∗ ⌜repr_lval θ' lv w⌝ ∗ block_sim v lv ∗ Φ v ∗
       at_boundary wrap_lang }}.
Proof.
  intros Hpeemp.
  iLöb as "IH" forall (eml).
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  rewrite wp_unfold. rewrite /wp_pre.
  iIntros "Hnb Hnprim HWP %st Hst".
  iDestruct (SI_not_at_boundary_is_in_ML with "Hst Hnb") as %(ρml&σ&->).
  iNamed "Hst". iNamed "SIML".
  iDestruct (interp_ML_discarded_locs_pub with "HσML SIAχNone") as %Hpublocs.
  iMod ("HWP" $! σ nMLv with "[$HσML $HvML $HσMLdom]") as "[HWP|[HWP|HWP]]".
  (* value *)
  + iDestruct "HWP" as "(%x & -> & Hσ & Hret)".
    iPoseProof (wp_to_val (wrap_penv pe) E x with "Hnb") as "Hwp".
    iDestruct (weakestpre.wp_strong_mono_post with "[Hret] Hwp") as "Hwp";
      last first.
    { rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
      iApply ("Hwp" $! (MLState ρml σ)).
      iSplitL "Hσ". 1: by iExists _. iExists _. by iFrame. }
    { cbn. iIntros (v) "(%θ' & %lv & ? & ? & ? & ?)". iExists _, _, _. iFrame. }
  (* extcall *)
  + iDestruct "HWP" as "(%fn_name & %vs & %K' & -> & %Hfn & >(%Ξ & Hσ & HT & Hr))".
    iAssert (⌜¬ is_prim_name fn_name⌝)%I with "[Hnprim HT]" as "%Hnprim".
    { destruct (decide (is_prim_name fn_name)) as [His|]; last by eauto.
      iExFalso. iApply "Hnprim"; eauto. }

    (* take an administrative step in the wrapper *)

    iModIntro. iRight; iRight.
    iSplit.
    { iPureIntro. exists (λ _, True). eapply head_prim_step.
      destruct (ml_to_c_exists vs ρml σ) as (ws & ρc & mem & ?); eauto.
      eapply MakeCallS; eauto.
      { rewrite language.to_of_class //. }
      { rewrite /wrap_penv /= lookup_prims_prog_None //. } }

    iIntros (X Hstep) "!>!>".
    apply wrap_step_call_inv in Hstep as (ws & ρc & mem & ? & ? & ?).
    iMod (wrap_interp_ml_to_c with "[- Hnb Hnprim Hr HT] Hnb") as "(Hσ & Hb & HGC & (%lvs & #Hblk & %))";
      first done.
    { rewrite /wrap_state_interp /ML_state_interp /named.
      iSplitL "Hσ"; first by iExists _. iExists _. by iFrame. }
    iModIntro. iExists _, _. iSplit; first done. iFrame "Hσ".

    (* step done; make an external call in the wrapper *)

    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iIntros (st') "Hst'".
    iDestruct (SI_at_boundary_is_in_C with "Hst' Hb") as %(ρc'&mem'&->).
    clear nCv.

    iModIntro. iRight; iLeft. iExists fn_name, ws, [K'].
    iSplit; first done. iSplit; first done.
    iFrame "Hb Hst'".
    iExists (λ wret, ∃ θ' vret lvret, GC θ' ∗ Ξ vret ∗ block_sim vret lvret ∗ ⌜repr_lval θ' lvret wret⌝)%I.
    iSplitL "HGC HT".
    { rewrite {2}/wrap_penv /wrap_proto /named /=. iExists _, _, _, _.
      iFrame "HGC HT Hblk". iSplit; first done.
      iIntros (? ? ? ?) "? ? ? %". iExists _, _, _. by iFrame. }
    iNext. iIntros (wret) "((%θ' & %vret & %lvret & HGC & HΞ & Hsim & %) & Hb)".

    (* extcall done; take an administrative step for the call return *)

    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iIntros (st') "Hst' !>". clear dependent ρc' mem' X.
    iDestruct (SI_at_boundary_is_in_C with "Hst' Hb") as %(ρc'&mem'&->). simpl.
    iRight; iRight. iSplit.
    { iPureIntro. exists (λ _, True). eapply head_prim_step.
      eapply RetS. eapply c_to_ml_True. }
    iIntros (X Hstep).
    apply wrap_step_ret_inv in Hstep.
    iMod (wrap_interp_c_to_ml with "Hst' HGC Hb Hsim") as "HH";
      [ done | done | ].
    iDestruct "HH" as "(%ρml' & %σ' & %HX & Hst & Hnb)".
    do 3 iModIntro. iExists _, _. iSplit; first done. iFrame "Hst".

    (* continue execution using IH *)

    iApply ("IH" with "Hnb Hnprim"). by iApply "Hr".

  (* step *)
  + iDestruct "HWP" as "(%Hred & HWP)".
    iModIntro. iRight. iRight. iSplit.
    * iPureIntro. exists (fun _ => True). eapply head_prim_step.
      destruct Hred as (e' & σ' & Hprim). econstructor; last done.
      rewrite Hpeemp in Hprim. cbn. eapply Hprim.
    * iIntros (X Hstep).
      apply wrap_step_expr_inv in Hstep as (eml' & σ' & Hstep & ?);
        [| by rewrite Hpeemp in Hred].
      rewrite Hpeemp. iMod ("HWP" $! _ _ Hstep) as "HWP".
      do 2 iModIntro. iMod "HWP" as "(HσC & HWP')".
      iModIntro. iExists _, _. iSplitR; first by iPureIntro.
      iSplitR "HWP' Hnb Hnprim".
      { rewrite /weakestpre.state_interp /= /named.
        iSplitL "HσC"; first by iExists _. iExists _; by iFrame. }
      iApply ("IH" with "Hnb Hnprim HWP'").
Qed.

Lemma wp_base_primitives (pe : prog_environ ML_lang Σ) prim ws E Φ :
  penv_prog pe = ∅ → (* XXX *)
  (∀ fn_name vs Φ, ⌜is_prim_name fn_name⌝ -∗ penv_proto pe fn_name vs Φ -∗ False) -∗
  proto_prims pe E prim ws Φ -∗
  at_boundary wrap_lang -∗
  WP (WrSE (RunPrimitive prim ws)) @ (wrap_penv pe); E {{ w,
    at_boundary wrap_lang ∗ Φ w }}.
Proof.
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
    iRight; iRight. iSplit.
    { iPureIntro. eexists (λ _, True). eapply head_prim_step.
      eapply CallbackS; eauto. eapply c_to_ml_True. }
    iIntros (X Hstep).
    apply wrap_step_callback_inv in Hstep as (? & ? & ? & ? & Hrepr & ? & ?).
    pose proof (repr_lval_inj_1 _ _ _ _ Hθinj Hreprw Hrepr);
      simplify_map_eq; clear Hrepr.

    iMod (wrap_interp_c_to_ml with "Hst HGC Hb Hsim'") as "HH";
      [ done | done | ].
    iDestruct "HH" as "(%ρml & %σ & % & Hst & Hnb)".

    do 3 iModIntro. iExists _, _. iSplit; first done. iFrame "Hst".

    iApply (weakestpre.wp_wand with "[-Cont Hclos]").
    { iApply (wp_simulates with "Hnb Hnprims WPcallback"); done. }
    cbn. iIntros (v) "(%θ' & %lv & %vret & HGC & % & Hsim & Hψ & $)".
    iApply ("Cont" with "[$] [$] [$]"); eauto. }
Qed.

End Simulation.
