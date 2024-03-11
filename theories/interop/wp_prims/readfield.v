From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.interop Require Import state lang basics_resources.
From melocoton.interop Require Export prims weakestpre prims_proto.
From melocoton.interop.wp_prims Require Import common.
From melocoton.mlanguage Require Import weakestpre.
Import Wrap.

Section Laws.

Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.

Implicit Types P : iProp Σ.
Import mlanguage.

Lemma readfield_correct e : |- wrap_prog e :: readfield_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamedProto "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iAssert ⌜∃ m', ζC ρc !! γ = Some (Bvblock (m', (tg, vs0)))⌝%I as "%Helem2".
  { iDestruct "Hpto" as "(Hpto & _)".
    iDestruct (hgh_lookup_vblock with "GCHGH Hpto") as %(?&_&?). eauto. }
  destruct Helem2 as [m' Helem2].
  assert (∃ (vv:lval), vs0 !! (Z.to_nat i) = Some vv) as [vv Hvv].
  1: apply lookup_lt_is_Some; lia.
  assert (∃ w', repr_lval (θC ρc) vv w') as [w' Hw']. (* TODO: lemma? *)
  1: { inv_repr_lval. destruct vv as [vvz|vvl]; first (eexists; econstructor).
       destruct HGCOK as [HGCL HGCR].
       eapply elem_of_dom in HGCR as [w' Hw']; first (eexists; by econstructor).
       1: eapply elem_of_dom_2, H1.
       2: constructor; by eapply elem_of_list_lookup_2. eauto. }

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), e' = WrSE (ExprV w') ∧ σ' = CState ρc mem).
  iSplit. { iPureIntro; econstructor; eauto. }
  iIntros (? ? ? (? & ?)); simplify_eq.
  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply "Hcont". iFrame.
  iApply ("Cont" with "[- $Hpto]"). iSplit; last done.
  rewrite /GC /named. iExists _, _, σMLvirt, _. iExists _.
  iFrame. iPureIntro; split_and!; eauto.
Qed.

End Laws.
