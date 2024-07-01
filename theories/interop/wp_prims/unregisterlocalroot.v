From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.interop Require Import state lang basics_resources.
From melocoton.interop Require Export prims weakestpre prims_proto wp_utils.
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

Lemma unregisterlocalroot_correct e : |- wrap_prog e :: unregisterlocalroot_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamedProto "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree.
  iPoseProof (ghost_var_agree with "GCrootsf Hfc") as "->".
  destruct roots_fm as [| fm roots_fm ]; first by simpl.
  rewrite map_app in H2. simpl in H2.

  iApply wp_pre_cases_c_prim; [done..|].

  iExists (λ '(e', σ'),
    e' = WrSE (ExprO (OVal #0)) ∧
    σ' = CState {|
      χC := χC ρc;
      ζC := ζC ρc;
      θC := θC ρc;
      rootsC := (map dom roots_fm) ++ [dom roots_gm];
   |} mem).
  iSplit. { iPureIntro. econstructor; eauto. }
  iIntros (w' ρc' mem' (? & ?)); simplify_eq.

  iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots&GCroots)".
  iMod (ghost_var_update_halves with "GCrootsf Hfc") as "(GCrootsf&Hfc)".
  iDestruct "GCrootsm" as "(GCrootsfm&GCrootsm)".
  iDestruct "GCrootspto" as "(GCrootsfpto&GCrootspto)".

  iDestruct "Hlr" as "(%fm'&(Hlr1&%Hlr2))".
  iPoseProof (ghost_map_auth_agree with "Hlr1 GCrootsfm") as "->".

  (* TODO: Transform points to roots into points to C *)
  iDestruct "GCrootsfpto" as "(GCrootsfmpto&GCrootsfpto)".
  iAssert (∃ ws,
     ([∗ list] w; l ∈ ws; (elements r), l ↦C w)
   ∗ ([∗ list] w; v ∈ ws; (elements r), ⌜repr_lval (θC ρc) v w⌝))% I
   with "[GCrootsfmpto]" as "(%ws&Hws)".
   { iInduction (elements r) as [ | rhd rtl ] "HR".
     - iExists []. admit.
     - iPoseProof ("HR" with "GCrootsfmpto") as "(%ws&Hws)".
       admit. }

  do 3 iModIntro. iFrame. iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_outcome; first done.
  iApply "Hcont". iFrame.
  iApply "Cont". iFrame "Hfc Hws".
  iExists _, _, _, _, roots_fm, roots_gm, fc.
  unfold named. iFrame.
  iPureIntro. split_and!; eauto.
  - apply map_app.
  - simpl in Hrootslive. by apply Forall_inv_tail in Hrootslive.
Admitted.

End Laws.
