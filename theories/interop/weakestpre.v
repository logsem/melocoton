From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From melocoton.mlanguage Require Import mlanguage.
From melocoton.language Require Import language weakestpre.
From melocoton.mlanguage Require Import weakestpre.
From melocoton.interop Require Import lang state.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Import defs resources.
From melocoton.ml_lang Require Import lang lang_instantiation primitive_laws.
From melocoton.interop Require Import basics basics_resources.
Import Wrap.

(* Definition of the wrapper state interpretation and WP instance *)

Class wrapperGS Σ := WrapperGS {
  wrapperGS_basics :> wrapperBasicsGS Σ;
  wrapperGS_locsetGS :> ghost_varG Σ (gsetUR loc);
  wrapperGS_addrmapGS :> ghost_varG Σ (leibnizO addr_map);
  wrapperGS_at_boundary :> ghost_varG Σ (leibnizO bool);
  wrapperGS_var_lstoreGS :> ghost_varG Σ lstore;
  wrapperGS_var_lloc_mapGS :> ghost_varG Σ lloc_map;
  wrapperGS_γζ : gname;
  wrapperGS_γroots_set : gname;
  wrapperGS_γθ : gname;
  wrapperGS_γχ : gname;
  wrapperGS_γat_boundary : gname;
}.

Section WrapperWP.

Context {hlc : has_lc}.
Context {Σ : gFunctors}.
Context `{!heapGS_ML Σ, !heapGS_C Σ}.
Context `{!invGS_gen hlc Σ}.
Context `{!wrapperGS Σ}.

Notation MLval := ML_lang.val.
Notation Cval := C_intf.val.

Implicit Types P : iProp Σ.

Definition C_state_interp (ζ : lstore) (χ : lloc_map) (θ : addr_map) (roots : gset addr) : iProp Σ :=
    "SIζ" ∷ ghost_var wrapperGS_γζ (1/2) ζ
  ∗ "SIχ" ∷ ghost_var wrapperGS_γχ (1/2) χ
  ∗ "SIθ" ∷ ghost_var wrapperGS_γθ (1/2) θ
  ∗ "SIroots" ∷ ghost_var wrapperGS_γroots_set (1/2) roots
  ∗ "SIbound" ∷ ghost_var wrapperGS_γat_boundary (1/4) true.

Definition GC (θ : addr_map) : iProp Σ :=
  ∃ (ζ ζfreeze ζσ ζvirt : lstore) (χ χvirt : lloc_map) (σMLvirt : store)
    (roots_s : gset addr) (roots_m : gmap addr lval),
    "GCζ" ∷ ghost_var wrapperGS_γζ (1/2) ζ
  ∗ "GCχ" ∷ ghost_var wrapperGS_γχ (1/2) χ
  ∗ "GCθ" ∷ ghost_var wrapperGS_γθ (1/2) θ
  ∗ "GCroots" ∷ ghost_var wrapperGS_γroots_set (1/2) roots_s
  ∗ "GCζvirt" ∷ lstore_own_auth ζvirt
  ∗ "GCbound" ∷ ghost_var wrapperGS_γat_boundary (1/4) true
  ∗ "(GCσMLv & GCσdom)" ∷ state_interp (σMLvirt : language.language.state ML_lang)
  ∗ "GCχvirt" ∷ lloc_own_auth χvirt
  ∗ "GCχNone" ∷ ([∗ map] _↦ℓ ∈ pub_locs_in_lstore χvirt ζvirt, ℓ ↦M/)
  ∗ "GCrootsm" ∷ ghost_map_auth wrapperGS_γroots_map 1 roots_m
  ∗ "GCrootspto" ∷ ([∗ map] a ↦ v ∈ roots_m, ∃ w, a ↦C w ∗ ⌜repr_lval θ v w⌝)
  ∗ "%Hrootsdom" ∷ ⌜dom roots_m = roots_s⌝
  ∗ "%Hrootslive" ∷ ⌜roots_are_live θ roots_m⌝
  ∗ "%Hfreezeρ" ∷ ⌜freeze_lstore ζ ζfreeze⌝
  ∗ "%Hfreezeeq" ∷ ⌜ζfreeze = ζσ ∪ ζvirt⌝
  ∗ "%Hfreezedj" ∷ ⌜ζσ ##ₘ ζvirt⌝
  ∗ "%Hstore_blocks" ∷ ⌜is_store_blocks χvirt σMLvirt ζσ⌝
  ∗ "%Hother_blocks" ∷ ⌜dom ζvirt ⊆ dom χvirt⌝
  ∗ "%Hstore" ∷ ⌜is_store χvirt ζfreeze σMLvirt⌝
  ∗ "%Hχvirt" ∷ ⌜expose_llocs χ χvirt⌝
  ∗ "%Hχinj" ∷ ⌜lloc_map_inj χ⌝ (* TODO redundant? *)
  ∗ "%HGCOK" ∷ ⌜GC_correct ζfreeze θ⌝.

Definition GC_token_remnant (ζ : lstore) (χ : lloc_map) (roots_m : roots_map) : iProp Σ :=
   "GCζ" ∷ ghost_var wrapperGS_γζ (1/2) ζ
 ∗ "GCχ" ∷ ghost_var wrapperGS_γχ (1/2) χ
 ∗ "GCθ" ∷ ghost_var wrapperGS_γθ (1/2) (∅:addr_map)
 ∗ "GCroots" ∷ ghost_var wrapperGS_γroots_set (1/2) (dom roots_m)
 ∗ "GCrootsm" ∷ ghost_map_auth wrapperGS_γroots_map 1 (roots_m : gmap loc lval)
 ∗ "GCrootspto" ∷ ([∗ set] a ∈ (dom roots_m), a O↦C None).

Definition ML_state_interp (ζvirt : lstore) (χ : lloc_map) (roots : roots_map) (memC : memory) : iProp Σ :=
    "SIζ" ∷ ghost_var wrapperGS_γζ (1/2) ζvirt
  ∗ "SIχ" ∷ ghost_var wrapperGS_γχ (1/2) χ
  ∗ "SIθ" ∷ ghost_var wrapperGS_γθ (1/2) (∅ : addr_map)
  ∗ "SIroots" ∷ ghost_var wrapperGS_γroots_set (1/2) (dom roots)
  ∗ "SIbound" ∷ ghost_var wrapperGS_γat_boundary (1/2) false
  ∗ "SIζvirt" ∷ lstore_own_auth ζvirt
  ∗ "HσCv" ∷ gen_heap_interp (memC ∪ (fmap (fun k => None) roots))
  ∗ "SIAχ" ∷ lloc_own_auth χ
  ∗ "SIAχNone" ∷ ([∗ map] _↦ℓ ∈ pub_locs_in_lstore χ ζvirt, ℓ ↦M/)
  ∗ "SIGCrem" ∷ GC_token_remnant ζvirt χ roots
  ∗ "%Hχinj" ∷ ⌜lloc_map_inj χ⌝
  ∗ "%Hother_blocks" ∷ ⌜dom ζvirt ⊆ dom χ⌝
  ∗ "%HmemCdisj" ∷ ⌜dom memC ## dom roots⌝.

Definition public_state_interp : memory → iProp Σ := gen_heap_interp.
Definition private_state_interp : wrapstateC → iProp Σ :=
  (λ ρc, C_state_interp (ζC ρc) (χC ρc) (θC ρc) (rootsC ρc))%I.

Definition wrap_state_interp (σ : Wrap.state) : iProp Σ :=
  match σ with
  | Wrap.CState ρc mem =>
      "HσC" ∷ public_state_interp mem ∗
      "SIC" ∷ private_state_interp ρc
  | Wrap.MLState ρml σ =>
      "(HσML & HσMLdom)" ∷ state_interp (σ:language.language.state ML_lang) ∗
      "SIML"             ∷ ML_state_interp (ζML ρml) (χML ρml) (rootsML ρml) (privmemML ρml)
end.

Global Program Instance wrapGS :
  mlanguage.weakestpre.mlangGS _ Σ wrap_lang
:= {
  state_interp := wrap_state_interp;
  at_boundary := (ghost_var wrapperGS_γat_boundary (1/2) true)%I;
}.

Definition not_at_boundary := (ghost_var wrapperGS_γat_boundary (1/2) false)%I.

Global Program Instance wrap_linkableGS : linkableGS wrap_lang public_state_interp := {
  private_state_interp := private_state_interp
}.
Next Obligation.
  iIntros (σ pubσ privσ Hlink) "Hσ !>". inversion Hlink; subst. iApply "Hσ".
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

Lemma SI_GC_is_in_C {θ} :
  SI -∗ GC θ -∗
  ⌜∃ ρc mem, σ = CState ρc mem⌝.
Proof.
  destruct σ. 2: iIntros "_ _"; iPureIntro; do 2 eexists; done.
  iNamed 1. iNamed 1. iNamed "SIML".
  iPoseProof (ghost_var_agree with "SIbound GCbound") as "%Hc".
  congruence.
Qed.

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

End WrapperWP.

Ltac SI_GC_agree :=
  iDestruct (ghost_var_agree with "GCζ SIζ") as %?;
  iDestruct (ghost_var_agree with "GCχ SIχ") as %?;
  iDestruct (ghost_var_agree with "GCθ SIθ") as %?;
  iDestruct (ghost_var_agree with "GCroots SIroots") as %?;
  simplify_eq.
