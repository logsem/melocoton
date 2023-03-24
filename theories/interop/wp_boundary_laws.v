From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import lang state.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Import defs resources.
From melocoton.ml_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.interop Require Import weakestpre wp_utils.
Import Wrap.

(* lemmas to switch between the ML<->C state interp at a boundary *)

Section BoundaryLaws.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Lemma wrap_interp_c_to_ml w ρc mem θ v lv (X : val → wrapstateML → store → Prop) :
  repr_lval θ lv w →
  c_to_ml w ρc mem X →
  wrap_state_interp (Wrap.CState ρc mem) -∗
  GC θ -∗
  at_boundary wrap_lang -∗
  lv ~~ v
  ==∗
  ∃ ρml σ,
  ⌜X v ρml σ⌝ ∗
  wrap_state_interp (Wrap.MLState ρml σ) ∗
  not_at_boundary.
Proof.
  iIntros (Hlv Hc_to_ml) "Hσ HGC Hnb #Hblk".
  iNamed "Hσ". iNamed "SIC". iNamed "HGC". simplify_eq. SI_GC_agree.

  iAssert (⌜is_val χvirt (ζσ ∪ ζvirt) v lv⌝)%I as "%Hval".
  by iApply (block_sim_auth_is_val with "GCχvirt GCζvirt Hblk").
  iAssert (⌜∀ k lv, roots_m !! k = Some lv →
            ∃ w, mem !! k = Some (Storing w) ∧ repr_lval (θC ρc) lv w⌝)%I as "%Hroots".
  1: { iIntros (kk vv Hroots).
       iPoseProof (big_sepM_lookup with "GCrootspto") as "(%wr & Hwr & %Hw2)"; first done.
       iExists wr. iSplit; last done. iApply (gen_heap_valid with "HσC Hwr"). }
  apply map_Forall_lookup_2 in Hroots.
  iMod (ghost_var_update_halves with "Hnb SIbound") as "(Hb & SIbound)".
  destruct (make_repr (θC ρc) roots_m mem) as [privmem Hpriv]; try done.
  iMod (ghost_var_update_halves with "GCζ SIζ") as "(GCζ & SIζ)".
  iMod (ghost_var_update_halves with "GCχ SIχ") as "(GCχ & SIχ)".
  iMod (ghost_var_update_halves with "GCθ SIθ") as "(GCθ & SIθ)".
  iMod (ghost_var_update_halves with "GCroots SIroots") as "(GCroots & SIroots)".
  iMod (set_to_none with "HσC GCrootspto") as "(HσC & GCrootspto)"; first done.

  iModIntro. iExists _, _. iSplit.
  { iPureIntro. eapply (Hc_to_ml σMLvirt _ _ (ζσ ∪ ζvirt) ζσ χvirt ζvirt roots_m privmem).
    all: try done. by rewrite map_union_comm. }
  iSplitR "SIbound"; last by iFrame "SIbound".
  rewrite /= /named. iFrame "GCσMLv GCσdom".
  unfold private_state_interp, ML_state_interp, GC_token_remnant, named; cbn.
  iFrame. iPureIntro; split_and!.
  1: destruct Hχvirt as (_ & HHH); apply HHH.
  1: apply Hother_blocks.
  1: destruct Hpriv as (mem_r & ->%repr_roots_dom & Hpriv2 & Hpriv3); by apply map_disjoint_dom.
Qed.

Lemma wrap_interp_ml_to_c vs ρml σ ws ρc mem :
  ml_to_c vs ρml σ ws ρc mem →
  wrap_state_interp (Wrap.MLState ρml σ) -∗
  not_at_boundary
  ==∗
  wrap_state_interp (Wrap.CState ρc mem) ∗
  at_boundary wrap_lang ∗
  GC (θC ρc) ∗
  (∃ lvs, lvs ~~∗ vs ∗ ⌜Forall2 (repr_lval (θC ρc)) lvs ws⌝).
Proof.
  iIntros (Hml_to_c) "Hst Hb".
  iNamed "Hst". iNamed "SIML". iNamed "SIGCrem".
  destruct Hml_to_c as (ζσ & ζnewimm & lvs & HH).
  destruct HH as (Hmono & Hblocks & Hprivblocks & HζC & Hζdisj &
                    Hstore & Hvals & ? & ? & ? & Hroots & ?).

  iDestruct (ghost_var_split _ _ (1/2) (1/2) with "[SIinit]") as "[SIinit GCinit]".
  { rewrite {1}(_: 1 = 1/2+1/2)%Qp // Qp.half_half //. }
  iMod (ghost_var_update_halves with "Hb SIbound") as "(Hnb & SIbound)".
  iMod (ghost_var_update_halves with "SIζ GCζ") as "(SIζ & GCζ)".
  iMod (ghost_var_update_halves with "SIχ GCχ") as "(SIχ & GCχ)".
  iMod (ghost_var_update_halves with "SIθ GCθ") as "(SIθ & GCθ)".
  iMod (ghost_var_update_halves with "SIroots GCroots") as "(SIroots & GCroots)".
  apply map_disjoint_union_r in Hζdisj as [Hζdisj1 Hζdisj2].
  iMod (lstore_own_insert_many with "SIζvirt") as "(SIζvirt & SIζnewimm)"; first done.
  iMod (lloc_own_mono with "SIAχ") as "SIAχ"; first done.
  assert (ζσ ##ₘ ζnewimm) as Hdisj2 by by eapply is_store_blocks_is_private_blocks_disjoint.
  assert (ζC ρc = ζσ ∪ (ζML ρml ∪ ζnewimm)) as H6B.
  1: { rewrite map_union_assoc. rewrite (map_union_comm ζσ); first done. by symmetry. }
  iPoseProof (block_sim_arr_of_auth _ _ _ _ _ vs lvs with "SIAχ SIζvirt") as "#Hsim".
  5: eassumption. 1-3:done. 1: by apply map_disjoint_union_r.
  iMod (set_to_some with "HσCv GCrootspto") as "(HσCv & GCrootspto)"; first done.

  iModIntro. iFrame "Hnb". rewrite /= /named.
  iFrame "HσCv SIζ SIχ SIθ SIroots SIbound".
  iSplitL "SIinit". { iExists false. iFrame. }
  iSplit.
  { rewrite /GC /named.
    iExists (ζC ρc), (ζC ρc), ζσ, (ζML ρml ∪ ζnewimm).
    iExists (χC ρc), (χC ρc), σ, (rootsC ρc), (rootsML ρml).
    iFrame. iSplit.
    { rewrite pub_locs_in_lstore_insert_priv_store; last done.
      erewrite pub_locs_in_lstore_mono at 1; [| eauto..]; [].
      iFrame "SIAχNone". }
    iPureIntro; split_and!; eauto.
    { reflexivity. }
    { by apply map_disjoint_union_r. }
    { rewrite dom_union_L. apply union_least.
      - etransitivity; [ eapply Hother_blocks |].
        eapply subseteq_dom, Hmono.
      - eapply elem_of_subseteq. intros γ Hγ.
        by eapply elem_of_dom_2, Hprivblocks. }
    { split; first done. split; first apply Hmono.
      intros γ v1 v2 HH1 HH2. simplify_map_eq. econstructor. } }
  { iExists _; by iFrame "Hsim". }
Qed.

End BoundaryLaws.
