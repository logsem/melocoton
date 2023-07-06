From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import lang state.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Import defs resources.
From melocoton.ml_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.interop Require Export basics basics_resources gctoken.
Import Wrap.

(** Definition of the wrapper state interpretation and WP instance *)

Class wrapperG `{!indexT} Σ := WrapperG {
  wrapperG_GCtok :> wrapperGCtokG Σ;
  wrapperG_γat_boundary : gname;
}.

Definition wrapperΣ {SI: indexT} : gFunctors :=
  #[wrapperBasicsΣ; wrapperGCtokΣ].

Global Instance subG_wrapperΣ_wrapperBasicsGpre `{SI: indexT} Σ :
  subG wrapperΣ Σ → wrapperBasicsGpre Σ.
Proof. solve_inG. Qed.
Global Instance subG_wrapperΣ_wrapperGCtokGpre `{SI: indexT} Σ :
  subG wrapperΣ Σ → wrapperGCtokGpre Σ.
Proof. solve_inG. Qed.

Section WrapperWP.

Context `{SIdx: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!invG Σ}.
Context `{!wrapperG Σ}.

Notation MLval := ML_lang.val.
Notation Cval := C_intf.val.

Implicit Types P : iProp Σ.

Definition preGCtok : iProp Σ :=
    "GCζ" ∷ ghost_var wrapperG_γζ (1/2) (∅:lstore)
  ∗ "GCχ" ∷ ghost_var wrapperG_γχ (1/2) (∅:lloc_map)
  ∗ "GCθ" ∷ ghost_var wrapperG_γθ (1/2) (∅:addr_map)
  ∗ "GCroots" ∷ ghost_var wrapperG_γroots_set (1/2) (∅:gset addr)
  ∗ "GCζauth" ∷ lstore_own_auth (∅:lstore)
  ∗ "GCML" ∷ state_interp (∅ : language.language.state ML_lang)
  ∗ "GCχauth" ∷ lloc_own_auth (∅:lloc_map)
  ∗ "GCrootsm" ∷ ghost_map_auth wrapperG_γroots_map 1 (∅:gmap addr lval).

Definition C_state_interp (ζ : lstore) (χ : lloc_map) (θ : addr_map) (roots : gset addr) : iProp Σ :=
  ∃ (at_init : bool),
    "SIζ" ∷ ghost_var wrapperG_γζ (1/2) ζ
  ∗ "SIχ" ∷ ghost_var wrapperG_γχ (1/2) χ
  ∗ "SIθ" ∷ ghost_var wrapperG_γθ (1/2) θ
  ∗ "SIroots" ∷ ghost_var wrapperG_γroots_set (1/2) roots
  ∗ "SIbound" ∷ ghost_var wrapperG_γat_boundary (1/2) true
  ∗ "SIinit" ∷ ghost_var wrapperG_γat_init (1/2) at_init
  ∗ "Hinit" ∷ if at_init then preGCtok else True.


Definition per_location_invariant_ML (ζ ζvirt : lstore)
     (γ : lloc) (ℓ : loc) : iProp Σ :=
  ∃ (vs : list val) lvs, 
    (⌜ζ !! γ = None⌝ ∗ γ ↦mut (TagDefault, lvs) ∗ ℓ ↦Mlen (length lvs))
  ∨ (⌜ζ !! γ = None⌝ ∗ ⌜ζvirt !! γ = None⌝).

Definition SI_block_level_ML (ζ : lstore) (χ : lloc_map) : iProp Σ :=
  ∃ ζvirt,
    "GCχauth" ∷ lloc_own_auth χ
  ∗ "GCζauth" ∷ lstore_own_auth (ζ ∪ ζvirt)
  ∗ "%Hother_blocks" ∷ ⌜dom ζ ⊆ dom χ⌝
  ∗ "%Hvirt" ∷ ⌜∀ γ, γ ∈ dom ζvirt → ∃ fid ℓ, χ !! γ = Some (LlocPublic fid ℓ)⌝
  ∗ "%Hdisj" ∷ ⌜ζ ##ₘ ζvirt⌝
  ∗ "GCχNone" ∷ ([∗ map] γ↦ℓ ∈ lloc_map_pubs χ,
      per_location_invariant_ML ζ ζvirt γ ℓ).

Definition SI_GC_ML (ζ : lstore) (roots_m : roots_map) : iProp Σ :=
    "GCrootsm" ∷ ghost_map_auth wrapperG_γroots_map 1 roots_m
  ∗ "GCrootspto" ∷ ([∗ map] a ↦ _ ∈ roots_m, a O↦C None).

Definition GC_remnant_ML (roots_m : roots_map) : iProp Σ :=
  ∃ (ζ : lstore) (χ : lloc_map),
    "GCζ" ∷ ghost_var wrapperG_γζ (1/2) ζ
  ∗ "GCχ" ∷ ghost_var wrapperG_γχ (1/2) χ
  ∗ "GCθ" ∷ ghost_var wrapperG_γθ (1/2) (∅ : addr_map)
  ∗ "GCroots" ∷ ghost_var wrapperG_γroots_set (1/2) (dom roots_m)
  ∗ "GCinit" ∷ ghost_var wrapperG_γat_init (1/2) false
  ∗ "HSI_block_level" ∷ SI_block_level_ML ζ χ
  ∗ "HSI_GC" ∷ SI_GC_ML ζ roots_m
  ∗ "%Hχinj" ∷ ⌜lloc_map_inj χ⌝.


Definition ML_state_interp (ζ : lstore) (χ : lloc_map) (roots : roots_map) (memC : memory) : iProp Σ :=
    "SIζ" ∷ ghost_var wrapperG_γζ (1/2) ζ
  ∗ "SIχ" ∷ ghost_var wrapperG_γχ (1/2) χ
  ∗ "SIθ" ∷ ghost_var wrapperG_γθ (1/2) (∅ : addr_map)
  ∗ "SIroots" ∷ ghost_var wrapperG_γroots_set (1/2) (dom roots)
  ∗ "SIbound" ∷ ghost_var wrapperG_γat_boundary (1/2) false
  ∗ "SIinit" ∷ ghost_var wrapperG_γat_init (1/2) false
  ∗ "SIGCrem" ∷ GC_remnant_ML roots
  ∗ "HσCv" ∷ gen_heap_interp (memC ∪ (fmap (fun k => None) roots))
  ∗ "%HmemCdisj" ∷ ⌜dom memC ## dom roots⌝.

Definition private_state_interp : wrapstateC → iProp Σ :=
  (λ ρc, C_state_interp (ζC ρc) (χC ρc) (θC ρc) (rootsC ρc))%I.

Definition wrap_state_interp (σ : Wrap.state) : iProp Σ :=
  match σ with
  | Wrap.CState ρc mem =>
      "HσC" ∷ public_state_interp mem ∗
      "SIC" ∷ private_state_interp ρc
  | Wrap.MLState ρml σ =>
      "HσML" ∷ state_interp (σ:language.language.state ML_lang) ∗
      "SIML"             ∷ ML_state_interp (ζML ρml) (χML ρml) (rootsML ρml) (privmemML ρml)
end.

Global Program Instance wrapG :
  mlanguage.weakestpre.mlangG _ wrap_lang Σ
:= {
  state_interp := wrap_state_interp;
  at_boundary := ghost_var wrapperG_γat_boundary (1/2) true
}.

Definition not_at_boundary := ghost_var wrapperG_γat_boundary (1/2) false.

Global Program Instance wrap_linkableG : linkableG wrap_lang public_state_interp := {
  private_state_interp := private_state_interp
}.
Next Obligation.
  iIntros (σ pubσ privσ Hlink) "Hσ". inversion Hlink; subst.
  iApply "Hσ".
Qed.
Next Obligation.
  iIntros (pubσ privσ) "Hpubσ Hprivσ !>". cbn.
  iExists (CState privσ pubσ). cbn. iSplitL; by iFrame.
Qed.
Next Obligation.
  intros [ρc mem|ρml σ]; iIntros "Hb Hσ".
  + iExFalso. iAssert (⌜true = false⌝)%I as "%Hdone".
    * iApply (ghost_var_agree with "Hb [Hσ]").
      iNamed "Hσ". iNamed "SIML". iFrame.
    * iPureIntro. congruence.
  + iExists _, _. iPureIntro. econstructor.
Qed.

Context (σ : Wrap.state).
Notation SI := (weakestpre.state_interp σ).

Lemma SI_at_boundary_is_in_C :
  SI -∗ at_boundary wrap_lang -∗
  ⌜∃ ρc mem, σ = CState ρc mem⌝.
Proof.
  iIntros "Hσ Hnb". destruct σ as [ρml σ' | ρc mem]; eauto.
  iExFalso. iNamed "Hσ"; iNamed "SIML".
  iPoseProof (ghost_var_agree with "Hnb SIbound") as "%HH"; congruence.
Qed.

Lemma SI_not_at_boundary_is_in_ML :
  SI -∗ not_at_boundary -∗
  ⌜∃ ρml s, σ = MLState ρml s⌝.
Proof.
  iIntros "Hσ Hnb". destruct σ as [ρml σ' | ρc mem]; eauto.
  iExFalso. iNamed "Hσ"; iNamed "SIC".
  iPoseProof (ghost_var_agree with "Hnb SIbound") as "%HH"; congruence.
Qed.

Lemma GC_per_loc_ML_insert M ζ ζσ γ' blk:
   M !! γ' = None →
(([∗ map] γ↦ℓ ∈ M, per_location_invariant_ML ζ ζσ γ ℓ)
⊢ [∗ map] γ↦ℓ ∈ M, per_location_invariant_ML ζ (<[ γ' := blk ]> ζσ) γ ℓ)%I.
Proof.
  iIntros (Hnℓ) "Hbig".
  iApply (big_sepM_wand with "Hbig").
  iApply (big_sepM_intro).
  iIntros "!>" (γ2 ℓ Hne) "(%vs'&%lvs&[(%H1&Hζ&Hlen)|(%H1&%H2)])"; iExists vs', lvs.
  - iLeft. iFrame. done.
  - iRight. iFrame. iSplit; first done.
    iPureIntro. rewrite lookup_insert_ne; first done.
    intros ->. congruence.
Qed.

Lemma GC_per_loc_ML_delete M ζ ζσ γ':
   M !! γ' = None →
(([∗ map] γ↦ℓ ∈ M, per_location_invariant_ML ζ ζσ γ ℓ)
⊢ [∗ map] γ↦ℓ ∈ M, per_location_invariant_ML ζ (delete γ' ζσ) γ ℓ)%I.
Proof.
  iIntros (Hnℓ) "Hbig".
  iApply (big_sepM_wand with "Hbig").
  iApply (big_sepM_intro).
  iIntros "!>" (γ2 ℓ Hne) "(%vs'&%lvs&[(%H1&Hζ&Hlen)|(%H1&%H2)])"; iExists vs', lvs.
  - iLeft. iFrame. done.
  - iRight. iFrame. iSplit; first done.
    iPureIntro. rewrite lookup_delete_ne; first done.
    intros ->. congruence.
Qed.

Lemma delete_lookup_None {A B} `{Countable A} (m : gmap A B) k1 k2 : m !! k2 = None → delete k1 m !! k2 = None.
Proof.
  intros Hn. destruct (EqDecision0 k1 k2).
  - subst. apply lookup_delete.
  - by rewrite lookup_delete_ne.
Qed.

Lemma GC_per_loc_ML_delete_2 M ζ ζσ γ':
   M !! γ' = None →
(([∗ map] γ↦ℓ ∈ M, per_location_invariant_ML ζ ζσ γ ℓ)
⊢ [∗ map] γ↦ℓ ∈ M, per_location_invariant_ML (delete γ' ζ) ζσ γ ℓ)%I.
Proof.
  iIntros (Hnℓ) "Hbig".
  iApply (big_sepM_wand with "Hbig").
  iApply (big_sepM_intro).
  iIntros "!>" (γ2 ℓ Hne) "(%vs'&%lvs&[(%H1&Hζ&Hlen)|(%H1&%H2)])"; iExists vs', lvs.
  - iLeft. iFrame. iPureIntro.
    by apply delete_lookup_None.
  - iRight. iFrame. iSplit; last done. iPureIntro.
    by apply delete_lookup_None.
Qed.

End WrapperWP.

Ltac SI_GC_agree :=
  iDestruct (ghost_var_agree with "GCζ SIζ") as %?;
  iDestruct (ghost_var_agree with "GCχ SIχ") as %?;
  iDestruct (ghost_var_agree with "GCθ SIθ") as %?;
  iDestruct (ghost_var_agree with "GCroots SIroots") as %?;
  iDestruct (ghost_var_agree with "GCinit SIinit") as %?;
  simplify_eq.
