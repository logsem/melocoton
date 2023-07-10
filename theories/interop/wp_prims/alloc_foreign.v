From iris.proofmode Require Import proofmode.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From melocoton Require Import named_props stdpp_extra.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.c_interface Require Import defs notation resources.
From melocoton.interop Require Import state lang basics_resources.
From melocoton.interop Require Import basics wp_utils.
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

(* TODO: refactor to share proof with wp_prim_alloc *)
Lemma alloc_foreign_correct e : |- wrap_prog e :: alloc_foreign_proto.
Proof using.
  iIntros (? ? ? ?) "H". unfold mprogwp. iNamed "H".
  iSplit; first done.
  iIntros (Φ') "Hb Hcont". iApply wp_wrap_call; first done. cbn [snd].
  rewrite weakestpre.wp_unfold. rewrite /weakestpre.wp_pre.
  iIntros "%σ Hσ". cbn -[wrap_prog].
  SI_at_boundary. iNamed "HGC". SI_GC_agree. iNamed "HSI_GC". iNamed "HSI_block_level".
  iAssert (⌜∀ k lv, roots_m !! k = Some lv →
            ∃ w, mem !! k = Some (Storing w) ∧ repr_lval (θC ρc) lv w⌝)%I as "%Hroots".
  1: { iIntros (kk vv Hroots).
       iPoseProof (big_sepM_lookup with "GCrootspto") as "(%wr & Hwr & %Hw2)"; first done.
       iExists wr. iSplit; last done. iApply (gen_heap_valid with "HσC Hwr"). }
  destruct (make_repr (θC ρc) roots_m mem) as [privmem Hpriv]; try done.

  assert (GC_correct (ζC ρc) (θC ρc) (χC ρc)) as HGC'.
  { eapply GC_correct_transport_rev; last done; done. }

  iApply wp_pre_cases_c_prim; [done..|].
  iExists (λ '(e', σ'), ∃ γ fid χC' ζC' θC' (a:loc) mem',
    χC ρc !! γ = None ∧
    (∀ γ' vis', γ ≠ γ' → (χC ρc) !! γ' = Some vis' → fid ≠ lloc_visibility_fid vis') ∧
    χC' = <[γ := LlocForeign fid]> (χC ρc) ∧
    ζC' = <[γ := Bforeign None]> (ζC ρc) ∧
    GC_correct ζC' θC' χC' ∧
    repr θC' _ _ _ ∧
    roots_are_live θC' _ ∧
    θC' !! γ = Some a ∧
    e' = WrSE (ExprV #a) ∧
    σ' = CState {| χC := χC'; ζC := ζC'; θC := θC'; rootsC := rootsC ρc |} mem').
  iSplit. { iPureIntro. econstructor; naive_solver. }
  iIntros (? ? ? (γ & fid & χC' & ζC' & θC' & a & mem' &
                  HγNone & Hfidfresh & -> & -> & HGCOK' & Hrepr' & Hrootslive' & ?)).
  destruct_and!; simplify_eq.

  assert (χ_future !! γ = None) as Hχfutγ.
  { eapply not_elem_of_dom. destruct Hχfuture as [<- _].
    by eapply not_elem_of_dom. }
  assert (ζ_future !! γ = None) as Hζfutγ.
  { eapply not_elem_of_dom. eintros H%elem_of_weaken; last done.
    by eapply not_elem_of_dom in Hχfutγ. }
  assert (ζC ρc !! γ = None) as HζCγ.
  { destruct Hζfuture as [HL HR]. eapply not_elem_of_dom. rewrite HL.
    eapply not_elem_of_dom in Hζfutγ; done. }

  eassert (freeze_lstore (<[γ := _]> (ζC ρc)) (<[γ:=_]> ζ_future)) as Hζfuturenew.
  { destruct Hζfuture as [HfL HfR]; split.
    - by erewrite !dom_insert_L, HfL.
    - intros γ1 b1 b2 ?%lookup_insert_Some ?%lookup_insert_Some.
      destruct_or!; destruct_and!; simplify_eq; eauto. }

  iMod (set_to_none _ _ _ _ Hpriv with "HσC GCrootspto") as "(HσC&GCrootspto)".
  iMod (set_to_some _ _ _ _ Hrepr' with "HσC GCrootspto") as "(HσC&GCrootspto)".

  iMod (ghost_var_update_halves with "GCζ SIζ") as "(GCζ&SIζ)".
  iMod (ghost_var_update_halves with "GCχ SIχ") as "(GCχ&SIχ)".
  iMod (ghost_var_update_halves with "GCθ SIθ") as "(GCθ&SIθ)".

  assert (∀ γ' vis'', γ ≠ γ' → χ_future !! γ' = Some vis'' → fid ≠ lloc_visibility_fid vis'') as Hfidfresh2.
  { intros γ' vis' Hne Hfut ->.
    destruct Hχfuture as (HH1&HH2&HH3).
    destruct ((χC ρc) !! γ') as [vis'1|] eqn:Heqold.
    2: eapply not_elem_of_dom in Heqold; eapply elem_of_dom_2 in Hfut; 
       by rewrite HH1 in Heqold.
    eapply Hfidfresh. 1: exact Hne. 1: done.
    epose proof (HH3 _ _ _ Heqold Hfut) as HH. inversion HH; simplify_eq; done. }

  iMod (lstore_own_insert _ γ _ with "GCζauth") as "(GCζauth & Hbp1)". 1: done.
  iMod (lloc_own_allocate_foreign _ γ fid with "[] GCχauth") as "(GCχauth&Hbp2)". 1-2: done.

  do 3 iModIntro. iFrame. cbn -[wrap_prog].
  iSplitL "SIinit". { iExists false. iFrame. }
  iApply wp_value; first done.
  iApply "Hcont". iFrame.
  iApply ("Cont" $! θC' γ with "[-Hbp2 Hbp1] [Hbp2 $Hbp1] []"); try done.
  3: iPureIntro; by econstructor.
  2: iSplit; try done; by iExists _.
  rewrite /GC /named.
  do 5 iExists _. iFrame.
  iSplitL "GCσMLv GC_per_loc". 2: iSplit; last iSplit; try iPureIntro.
  - iExists σMLvirt. iFrame.
    iPoseProof (GC_per_loc_modify_ζ with "GC_per_loc") as "GC_per_loc".
    1: apply lloc_map_pubs_lookup_None; by left. unfold named.
    repeat iSplit; try iPureIntro.
    * rewrite dom_insert_L; set_solver.
    * rewrite lloc_map_pubs_insert_foreign delete_notin.
      2: apply lloc_map_pubs_lookup_None; by left. done.
    * intros ℓ Hℓ; destruct (Hstore _ Hℓ) as (γ'&fid'&Hγ'); exists γ', fid'; rewrite lookup_insert_ne; first done.
      intros ->; simplify_eq.
  - iExists roots_m. iFrame. iPureIntro; split_and!; try done.
    eapply GC_correct_transport; try done.
    by eapply expose_llocs_insert_foreign_both.
  - done.
  - by apply expose_llocs_insert_foreign_both.
Qed.

End Laws.
