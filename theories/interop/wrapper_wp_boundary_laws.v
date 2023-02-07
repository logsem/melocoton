From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import wrappersem wrapperstate.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Import proofmode.
From melocoton.c_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.ml_toy_lang Require Import lang melocoton.lang_instantiation melocoton.primitive_laws.
From melocoton.interop Require Import linking_wp basics basics_resources wrapper_wp
  wrapper_wp_block_sim wrapper_wp_utils.
Import Wrap.

(* lemmas to switch between the ML<->C state interp at a boundary *)

Section BoundaryLaws.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Notation MLval := ML_lang.val.
Notation Cval := C_lang.val.

Lemma wrap_interp_c_to_ml w ρc mem θ v lv (X : val → wrapstateML → store → Prop) :
  repr_lval θ lv w →
  c_to_ml w ρc mem X →
  wrap_state_interp (Wrap.CState ρc mem) -∗
  GC θ -∗
  not_at_boundary -∗
  block_sim v lv
  ==∗
  ∃ ρml σ,
  ⌜X v ρml σ⌝ ∗
  wrap_state_interp (Wrap.MLState ρml σ) ∗
  at_boundary _.
Proof.
  iIntros (Hlv Hc_to_ml) "Hσ HGC Hnb #Hblk".
  iNamed "Hσ". iNamed "SIC". iNamed "HGC". simplify_eq.

  iAssert (⌜is_val χvirt (ζσ ∪ ζrest) v lv⌝)%I as "%Hval".
  by iApply (block_sim_to_ghost_state with "HAχvirt HAζrest [] [] [] [] Hblk").
  iAssert (⌜∀ k lv, roots_m !! k = Some lv → ∃ w, mem !! k = Some (Storing w) ∧ repr_lval θ lv w⌝)%I as "%Hroots".
  1: { iIntros (kk vv Hroots).
       iPoseProof (big_sepM_lookup with "Hrootspto") as "(%wr & Hwr & %Hw2)"; first done.
       iExists wr. iSplit; last done. iApply (gen_heap_valid with "HσC Hwr"). }
  apply map_Forall_lookup_2 in Hroots.
  iPoseProof (ghost_var_agree with "HAGCθ HAθ") as "%Hagree1"; subst θ.
  iPoseProof (ghost_var_agree with "HArootss HAroots") as "%Hagree2".
  iMod (ghost_var_update_halves with "Hnb [HAGCbound HAbound]") as "(Hb & Hbound)".
  (* Coq fails to infer ghost_var_fractional in time *)
  1: iPoseProof (@fractional.fractional_merge _ _ _ _ _ _ (ghost_var_fractional _ _) with "HAGCbound HAbound") as "HH".
  1: by assert ((1 / 4 + 1 / 4 = 1 / 2)%Qp) as -> by compute_done.
  destruct (make_repr (θC ρc) roots_m mem) as [privmem Hpriv]; try done.
  iMod (ghost_var_update_halves with "HAGCθ HAθ") as "(HAGCθ & HAθ)".
  iMod (set_to_none with "HσC Hrootspto") as "(HσC & Hrootspto)"; first done.

  iModIntro. iExists _, _. iSplit.
  { iPureIntro. eapply (Hc_to_ml σMLvirt _ _ (ζσ ∪ ζrest) ζσ χvirt ζrest roots_m privmem).
    all: try done. by rewrite map_union_comm. }
  iSplitR "Hbound"; last by iFrame "Hbound".
  rewrite /= /named.
  iSplitL "HAσMLv HAnMLv HAσdom".
  { iExists nMLv; iFrame. }
  unfold private_state_interp, ML_state_interp, GC_token_remnant, named; cbn.
  iFrame. iSplitL "HnC"; first by iExists _.
  rewrite <- Hagree2.
  iFrame "HAroots".
  iPureIntro; split_and!.
  1: destruct Hχvirt as (_ & HHH); apply HHH.
  1: apply Hother_blocks.
  1: destruct Hpriv as (mem_r & ->%repr_roots_dom & Hpriv2 & Hpriv3); by apply map_disjoint_dom.
Qed.

Lemma wrap_interp_ml_to_c vs ρml σ ws ρc mem :
  ml_to_c vs ρml σ ws ρc mem →
  wrap_state_interp (Wrap.MLState ρml σ) -∗
  at_boundary wrap_lang
  ==∗
  wrap_state_interp (Wrap.CState ρc mem) ∗
  not_at_boundary ∗
  GC (θC ρc) ∗
  (∃ lvs, block_sim_arr vs lvs ∗ ⌜Forall2 (repr_lval (θC ρc)) lvs ws⌝).
Proof.
  iIntros (Hml_to_c) "Hst Hb".
  iNamed "Hst". iNamed "SIML". iNamed "HAGCrem".
  destruct Hml_to_c as (ζσ & ζnewimm & lvs & HH).
  destruct HH as (Hmono & Hblocks & Hprivblocks & HζC & Hζdisj &
                    Hstore & Hvals & ? & ? & ? & Hroots & ?).

  iMod (ghost_var_update_halves with "Hb HAbound") as "(Hnb & Hnb2)".
  1: iPoseProof (@fractional.fractional _ _ (ghost_var_fractional _ _)) as "[HH _]".
  iDestruct ("HH" with "[Hnb2]") as "(HAGCbound & HAbound)".
  1: by assert ((1 / 4 + 1 / 4 = 1 / 2)%Qp) as <- by compute_done.
  iClear "HH".
  iMod (ghost_var_update_halves with "HAθ HAGCθ") as "(HAθ & HAGCθ)".
  apply map_disjoint_union_r in Hζdisj as [Hζdisj1 Hζdisj2].
  iMod (lstore_own_insert_many with "HAζrest") as "(HAζrest & Hζnewimm)"; first done.
  iMod (lloc_own_mono with "HAχ") as "HAχ"; first done.
  assert (ζσ ##ₘ ζnewimm) as Hdisj2 by by eapply is_store_blocks_is_private_blocks_disjoint.
  assert (ζC ρc = ζσ ∪ (ζML ρml ∪ ζnewimm)) as H6B.
  1: { rewrite map_union_assoc. rewrite (map_union_comm ζσ); first done. by symmetry. }
  iPoseProof (block_sim_arr_of_ghost_state _ _ _ _ _ vs lvs with "HAχ HAζrest [] [] [] [] []") as "#Hsim".
  1-5: iPureIntro. 5: eassumption. 1-3:done. 1: by apply map_disjoint_union_r.
  iMod (set_to_some with "HAσCv Hrootspto") as "(HAσCv & Hrootspto)"; first done.

  iModIntro. iFrame "Hnb". rewrite /= /named.
  iSplitR "HAGCθ HAGCbound HArootsm HArootss Hrootspto".
  { iSplitL "HAσCv HAnCv". { iExists nCv. iFrame. }
    rewrite /C_state_interp /= /named.
    iExists (ζC ρc), ζσ, (ζML ρml ∪ ζnewimm), (χC ρc), σ. iFrame.
    rewrite Hroots. iFrame "HAroots".
    iSplitL "HvML"; first by iExists _.
    rewrite pub_locs_in_lstore_insert_priv_store; last done.
    erewrite pub_locs_in_lstore_mono at 1; [| eauto..]; [].
    iFrame "HAχNone".
    iPureIntro. split_and!; eauto.
    { reflexivity. }
    { by apply map_disjoint_union_r. }
    { rewrite dom_union_L. apply union_least.
      - etransitivity; [ eapply Hother_blocks |].
        eapply subseteq_dom, Hmono.
      - eapply elem_of_subseteq. intros γ Hγ.
        by eapply elem_of_dom_2, Hprivblocks. }
    { split; first done. split; first apply Hmono.
      intros γ v1 v2 HH1 HH2. simplify_map_eq. econstructor. } }
  { iSplitL; last by (iExists _; iFrame "Hsim").
    rewrite /GC /named. iExists (dom (rootsML ρml)), (rootsML ρml).
    iFrame. done. }
Qed.

End BoundaryLaws.
