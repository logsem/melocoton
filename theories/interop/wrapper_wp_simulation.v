From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem wrapperstate.
From iris.base_logic.lib Require Import ghost_map ghost_var gset_bij.
From iris.algebra Require Import gset gset_bij.
From melocoton Require Import big_sepM_limited.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.interop Require Import linking_wp basics wrapper_wp wrapper_wp_block_sim.
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


Notation mkPeC p T := ({| penv_prog := p; penv_proto := T |} : prog_environ _ Σ).
Notation mkPeW p T := ({| weakestpre.penv_prog := p; weakestpre.penv_proto := T |} : weakestpre.prog_environ wrap_lang Σ).


Definition WP_ext_call_spec : string -d> list Cval -d> (Cval -d> iPropO Σ) -d> iPropO Σ := λ n vl wp,
  ⌜False⌝%I.

Definition forbidden_function_names : list string := ["alloc"; "registerroot"; "unregisterroot"; "modify"; "readfield"; "int2val"; "val2int"].

Notation wrap_return := (fun Φ (a:Cval) => (∃ θ' l v, GC θ' ∗ Φ v ∗ ⌜repr_lval θ' l a⌝ ∗ block_sim v l)%I).


Lemma wp_to_val E p T a Φ: 
    wrap_return Φ a
 -∗ not_at_boundary
 -∗ WP (ExprC (C_lang.Val a)) @ (mkPeW (p : prog wrap_lang) T); E {{ v, Φ v ∗ at_boundary _}}.
Proof.
  iIntros "(%θ & %l & %v & HGC & Hv & %Hrepr & #Hblock) Hnb".
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ".
  iDestruct (GC_in_C with "Hσ HGC") as "%H"; destruct H as (ρc & mem & ->).
  iNamed "Hσ". iNamed "HGC". iNamed "SIC".
  iRight. iRight. iModIntro. iSplit.
  1: iPureIntro; cbn; exists (fun _ => True); eexists (), _; repeat split; by eapply RetS.
  cbn. iIntros (X Hstep).
  destruct Hstep as ([] & e1 & Heq & Hstep).
  cbv in Heq; subst e1.
  inversion Hstep.
  1: exfalso; apply language.language.val_stuck in H3; cbn in H3; done.
  2-8: exfalso; unfold language.to_call in H2; destruct language.to_class as [[]|] eqn:Heq; try congruence;
       destruct (language.fill_class' K ec) as [?|[vv ?]];
       [exists (ExprVal a); cbn; by rewrite H
       |subst K; cbn in *; subst ec; cbn in Heq; congruence| congruence].
  cbn in H3; injection H3; intros <-.
  iAssert (⌜is_val χvirt ζfreeze v l⌝)%I as "%Hval".
  1: iApply (block_sim_to_ghost_state with "HAχbij HAζbl"); done.

  iPoseProof (ghost_var_agree with "HAGCθ HAθ") as "->".
  iPoseProof (ghost_var_agree with "HArootss HAroots") as "->".
  iPoseProof (@fractional.fractional_merge _ (ghost_var wrapperGS_γat_boundary (1 / 4) false) (ghost_var wrapperGS_γat_boundary (1 / 4) false) _ (1/4) (1/4) (ghost_var_fractional _ _) with "HAGCbound HAbound") as "Hnb'".
  assert ((1 / 4 + 1 / 4 = 1 / 2)%Qp) as -> by compute_done.
  iMod (ghost_var_update_halves with "Hnb Hnb'") as "(Hnb & Hbound)".

  do 3 iModIntro. do 2 iExists _.  iSplit.
  1: iPureIntro; eapply (H4 σMLvirt l v ζfreeze ζσ χvirt ζrest roots_m mem).
  all: try done.
  1: rewrite map_union_comm; done.
  1: apply map_disjoint_dom_1; eapply map_disjoint_spec; intros ?????; by eapply map_disjoint_spec.
  1: admit.
  iSplitR "Hv Hnb"; last first.
  1: { cbn. unfold Wrap.fill. iApply weakestpre.wp_value'. iFrame. }
  cbn. iSplitL "HAσMLv HAnMLv".
  1: iExists nMLv; iFrame.
  unfold private_state_interp, ML_state_interp, named; cbn.
Admitted.

Lemma wp_simulates E p T ec Φ: 
    ⌜Forall (fun k => p !! k = None) forbidden_function_names⌝
 -∗ not_at_boundary
 -∗ WP ec @ (mkPeC p WP_ext_call_spec); E {{a, wrap_return Φ a }}
 -∗ WP (ExprC ec) @ (mkPeW (p : prog wrap_lang) T); E {{ v, Φ v ∗ at_boundary _}}.
Proof.
  iIntros "%Hforbid".
  iLöb as "IH" forall (ec).
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  rewrite wp_unfold. rewrite /wp_pre.
  iIntros "Hnb HWP %σ Hσ".
  destruct σ as [ρml σ | ρc mem].
  1: iExFalso; iClear "HWP"; iNamed "Hσ"; iNamed "SIML"; iPoseProof (ghost_var_agree with "Hnb HAbound") as "%HH"; congruence.
  iNamed "Hσ"; iNamed "SIC".
  iMod ("HWP" $! mem nCv with "HσC") as 
  "[(%x & -> & Hσ & Hret)
  |[(%s' & %vv & %K' & -> & %H2 & >(%Ξ & Hσ & HT & Hr))
  |(%Hred & H3)]]".
  + iPoseProof (wp_to_val with "Hret") as "Hret".
    iSpecialize ("Hret" with "Hnb").
    rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
    iApply ("Hret" $! (CState ρc mem)).
    iSplitL "Hσ". 1: by iExists _.
    unfold C_state_interp, named.
    iExists ζfreeze, ζσ, ζrest, χvirt, fresh, σMLvirt.
    iFrame. iFrame "HAζpers".
    iSplitL "HAnMLv"; first by iExists nMLv.
    iPureIntro. split_and!; done.
  + cbn. iExFalso. iApply "HT". (* TODO: add more calls here *)
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
      subst ec0 ρc0 mem0 X0. cbn.
      iMod ("H3" $! _ _ H3) as "H3".
      do 2 iModIntro. iMod "H3" as "(HσC & HWP')".
      iModIntro. iExists _, _. iSplitR; first (iPureIntro; apply H4).
      iSplitR "HWP' Hnb".
      2: iApply ("IH" with "Hnb HWP'").
      cbn. iSplitL "HσC"; first by iExists _.
      unfold C_state_interp, named. iExists ζfreeze, ζσ, ζrest, χvirt, fresh, σMLvirt.
      iFrame. iFrame "HAζpers". iSplitL; first by iExists _.
      iPureIntro; split_and!; done.
Qed.


Lemma run_function_correct F (vv : list ML_lang.val) T p E Φ: 
    ⌜arity F = length vv⌝
 -∗ at_boundary _
 -∗ (∀ θ ll aa ec, 
       GC θ 
    -∗ ⌜C_lang.apply_function F aa = Some ec⌝
    -∗ ([∗ list] l;a ∈ ll;aa, ⌜repr_lval θ l a⌝)
    -∗ block_sim_arr vv ll
    -∗ WP ec @ (mkPeC p WP_ext_call_spec); E {{a, wrap_return Φ a }})
 -∗ WP RunFunction F vv @ (mkPeW (p : prog wrap_lang) T); E {{ v, Φ v ∗ at_boundary _}}.
Proof.
  iIntros "%Harity Hb Hwp".
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros (σ) "Hσ".
  unfold at_boundary; cbn. destruct σ as [ρml σ | ? ?].
  2: {iExFalso. iNamed "Hσ"; iNamed "SIC". iPoseProof (ghost_var_agree with "Hb HAbound") as "%Heq". congruence. }
  iRight. iRight. iModIntro.
  iSplitR.
  1: { iPureIntro. exists (fun _ => True). eapply mlanguage.head_prim_step. cbn. eapply RunFunctionS; last done. all: admit. }
Admitted.

End Simulation.
