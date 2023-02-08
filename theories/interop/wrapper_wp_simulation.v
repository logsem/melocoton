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
From melocoton.interop Require Import linking_wp basics wrapper_wp wrapper_wp_block_sim
  wrapper_wp_utils wrapper_wp_ext_call_laws wrapper_wp_boundary_laws.
Import Wrap.

Section Simulation.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Context (p : language.prog C_lang).
Context (Hforbid : Forall (fun k => p !! k = None) forbidden_function_names).

Notation MLval := ML_lang.val.
Notation Cval := C_lang.val.

Implicit Types P : iProp Σ.
Import mlanguage.


Notation mkPeC p T := ({| penv_prog := p; penv_proto := T |} : prog_environ _ Σ).
Notation mkPeW p T := ({| weakestpre.penv_prog := p; weakestpre.penv_proto := T |} : weakestpre.prog_environ wrap_lang Σ).

Notation wrap_return := (fun Φ (a:Cval) => (∃ θ' l v, GC θ' ∗ Φ v ∗ ⌜repr_lval θ' l a⌝ ∗ block_sim v l)%I).

Lemma wp_to_val E T a Φ: 
    wrap_return Φ a (* Basically, a WP (Val a) {{a, wrap_return a}} *)
 -∗ not_at_boundary
 -∗ WP (ExprC (C_lang.Val a)) @ (mkPeW (p : prog wrap_lang) T); E {{ v, Φ v ∗ at_boundary _}}.
Proof.
  iIntros "(%θ & %l & %v & HGC & Hv & %Hrepr & #Hblock) Hnb".
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ".
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iModIntro. iRight. iRight. iSplit.
  { iPureIntro. cbn. exists (λ _, True); eexists (), _; repeat split.
    eapply RetS; eauto using c_to_ml_True. }

  cbn. iIntros (X Hstep).
  destruct Hstep as ([] & e1 & Heq & Hstep).
  cbv in Heq; subst e1.
  inversion Hstep.
  1: exfalso; apply language.language.val_stuck in H3; cbn in H3; done.
  2-8: exfalso; unfold language.to_call in H2; destruct language.to_class as [[]|] eqn:Heq; try congruence;
       destruct (language.fill_class' K ec) as [?|[vv ?]];
       [exists (ExprVal a); cbn; by rewrite H
       |subst K; cbn in *; subst ec; cbn in Heq; congruence| congruence].
  cbv [fill Wrap.fill wrap_lang] in *.
  cbn [C_lang.to_val] in *; simplify_eq.

  iMod (wrap_interp_c_to_ml with "Hσ HGC Hnb [$]") as "(%ρml & %σ & HH)"; [done..|].
  iDestruct "HH" as "(%HX & SI & Hb)".
  do 3 iModIntro. do 2 iExists _. iSplit; first done. iFrame "SI".
  iApply weakestpre.wp_value'. iFrame.
Qed.

Lemma wp_simulates E T ec Φ: 
    not_at_boundary
 -∗ WP ec @ (mkPeC p WP_ext_call_spec); E {{a, wrap_return Φ a }}
 -∗ WP (ExprC ec) @ (mkPeW (p : prog wrap_lang) T); E {{ v, Φ v ∗ at_boundary _}}.
Proof.
  iLöb as "IH" forall (ec).
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  rewrite wp_unfold. rewrite /wp_pre.
  iIntros "Hnb HWP %σ Hσ".
  destruct σ as [ρml σ | ρc mem].
  1: iExFalso; iClear "HWP"; iNamed "Hσ"; iNamed "SIML"; iPoseProof (ghost_var_agree with "Hnb HAbound") as "%HH"; congruence.
  iNamed "Hσ"; iNamed "SIC".
  iMod ("HWP" $! mem nCv with "[HσC HnC]") as 
  "[(%x & -> & Hσ & Hret)
  |[(%s' & %vv & %K' & -> & %H2 & >(%Ξ & Hσ & HT & Hr))
  |(%Hred & H3)]]".
  + cbn. iFrame.
  + iPoseProof (wp_to_val with "Hret") as "Hret".
    iSpecialize ("Hret" with "Hnb").
    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iApply ("Hret" $! (CState ρc mem)).
    iSplitL "Hσ". 1: by iExists _.
    unfold C_state_interp, named.
    iExists ζfreeze, ζσ, ζrest, χvirt, σMLvirt.
    iFrame.
    iSplitL "HAnMLv"; first by iExists nMLv.
    iPureIntro. split_and!; done.
  + iPoseProof (wp_ext_call_collect_all with "[] Hnb HT [Hr]") as "Hwp"; first done.
    1: iIntros "!> %r HΞ Hnb"; iApply ("IH" with "Hnb");
       by iApply "Hr".
    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iApply ("Hwp" $! (CState ρc mem)).
    iSplitL "Hσ". 1: by iExists _.
    unfold C_state_interp, named.
    iExists ζfreeze, ζσ, ζrest, χvirt, σMLvirt.
    iFrame.
    iSplitL "HAnMLv"; first by iExists nMLv.
    iPureIntro. split_and!; done.
  + cbn in Hred. iModIntro. iRight. iRight. iSplit.
    * iPureIntro. exists (fun _ => True). eapply head_prim_step.
      destruct Hred as (e' & σ' & Hprim). econstructor; last done. cbn. eapply Hprim.
    * iIntros (X Hstep).
      destruct Hstep as ([] & x & Hre & Hstep). cbv in Hre; subst x.
      cbn in Hstep; unfold step,mrel in Hstep; cbn in Hstep.
      inversion Hstep. 2-9: exfalso.
      2: { apply C_lang.of_to_val in H3; subst ec.
           apply language.language.reducible_no_threads_reducible in Hred.
           apply language.language.reducible_not_val in Hred. cbn in Hred; congruence. }
      2-8: subst ec; eapply reducible_call_is_in_prog; 
           [ by eapply language.language.reducible_no_threads_reducible
           | done
           | eapply @List.Forall_forall in Hforbid; [apply Hforbid | cbv; eauto 20]].
      cbv in H1,H4.
      subst ec0 ρc0 mem0 X0. cbn.
      iMod ("H3" $! _ _ H3) as "H3".
      do 2 iModIntro. iMod "H3" as "(HσC & HWP')".
      iModIntro. iExists _, _. iSplitR; first (iPureIntro; apply H4).
      iSplitR "HWP' Hnb".
      2: iApply ("IH" with "Hnb HWP'").
      cbn. iSplitL "HσC"; first by iExists _.
      unfold C_state_interp, named. iExists ζfreeze, ζσ, ζrest, χvirt, σMLvirt.
      iFrame. iSplitL; first by iExists _.
      iPureIntro; split_and!; done.
Qed.


Lemma run_function_correct F (vv : list ML_lang.val) T E Φ:
    ⌜arity F = length vv⌝
 -∗ at_boundary _
 -∗ (∀ θ ll aa ec,
       GC θ
    -∗ ⌜C_lang.apply_function F aa = Some ec⌝
    -∗ ⌜Forall2 (repr_lval θ) ll aa⌝
    -∗ block_sim_arr vv ll
    -∗ WP ec @ (mkPeC p WP_ext_call_spec); E {{a, wrap_return Φ a }})
 -∗ WP RunFunction F vv @ (mkPeW (p : prog wrap_lang) T); E {{ v, Φ v ∗ at_boundary _}}.
Proof.
  iIntros "%Harity Hb Hwp".
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros (σ) "Hσ".
  unfold at_boundary; cbn. destruct σ as [ρml σ | ? ?].
  2: {iExFalso. iNamed "Hσ"; iNamed "SIC". iPoseProof (ghost_var_agree with "Hb HAbound") as "%Heq". congruence. }
  iModIntro. iRight. iRight.
  iSplit.
  + iNamed "Hσ". iNamed "SIML".
    iDestruct (interp_ML_discarded_locs_pub with "HσML HAχNone") as %Hpublocs.
    iPureIntro. exists (fun _ => True). eapply mlanguage.head_prim_step. cbn.
    destruct (ml_to_c_exists vv ρml σ) as (ws & ρc & mem & Hml_to_c); eauto.
    destruct (apply_function_arity F ws) as (HL&_); destruct HL as (ec&Hec).
    { rewrite Harity. eapply ml_to_c_words_length; eauto. }
    eapply RunFunctionS; eauto.
  + iIntros (X Hstep).
    destruct Hstep as ([] & e1 & Heq & Hstep).
    cbv in Heq; subst e1.
    inversion Hstep.
    cbv [fill Wrap.fill wrap_lang] in *. simplify_eq.
    iMod (wrap_interp_ml_to_c with "Hσ [$]") as "(Hσ & Hnb & HGC & (%lvs & #Hblk & %))";
      first done.
    do 3 iModIntro. do 2 iExists _. iSplit; first by iPureIntro. iFrame "Hσ".
    iApply (wp_simulates with "Hnb").
    iApply ("Hwp" with "HGC [%] [%] [$]"); eauto.
Qed.

End Simulation.
