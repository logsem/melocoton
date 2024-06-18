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
From melocoton.interop Require Export basics basics_resources gctoken hybrid_ghost_heap.
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
  ∗ "GCroots" ∷ ghost_var wrapperG_γroots_set (1/2) ([∅]:list $ gset addr)
  ∗ "GCζvirt" ∷ lstore_own_auth (∅:lstore)
  ∗ "GCML" ∷ state_interp (∅ : language.language.state ML_lang)
  ∗ "GCχvirt" ∷ lloc_own_auth (∅:lloc_map)
  ∗ "GCrootsm" ∷ ghost_map_auth wrapperG_γroots_map 1 (∅:gmap addr lval).

Definition C_state_interp (ζ : lstore) (χ : lloc_map) (θ : addr_map) (roots_s : list $ gset addr) : iProp Σ :=
  ∃ (at_init : bool),
    "SIζ" ∷ ghost_var wrapperG_γζ (1/2) ζ
  ∗ "SIχ" ∷ ghost_var wrapperG_γχ (1/2) χ
  ∗ "SIθ" ∷ ghost_var wrapperG_γθ (1/2) θ
  ∗ "SIroots" ∷ ghost_var wrapperG_γroots_set (1/2) roots_s
  ∗ "SIbound" ∷ ghost_var wrapperG_γat_boundary (1/2) true
  ∗ "SIinit" ∷ ghost_var wrapperG_γat_init (1/2) at_init
  ∗ "Hinit" ∷ if at_init then preGCtok else True.

Definition GC_remnant (ζ : lstore) (χ : lloc_map) (roots_m : list roots_map) : iProp Σ :=
  ∃ (roots_f : list gname),
   "GCζ" ∷ ghost_var wrapperG_γζ (1/2) ζ
 ∗ "GCχ" ∷ ghost_var wrapperG_γχ (1/2) χ
 ∗ "GCθ" ∷ ghost_var wrapperG_γθ (1/2) (∅:addr_map)
 ∗ "GCHGH" ∷ HGH χ None ζ
 ∗ "GCinit" ∷ ghost_var wrapperG_γat_init (1/2) false
 ∗ "GCroots" ∷ ghost_var wrapperG_γroots_set (1/2) (map dom roots_m)
 ∗ "GCrootsf"  ∷ghost_var wrapperG_γroots_frame (1 / 2) roots_f
 ∗ "GCrootsm" ∷ ([∗ list] f; r ∈ roots_f;roots_m, ghost_map_auth f 1 r)
 ∗ "GCrootspto" ∷ ([∗ list] r ∈ roots_m, [∗ set] a ∈ (dom r), a O↦C None).

Definition ML_state_interp (ζ : lstore) (χ : lloc_map) (roots_m : list roots_map) (memC : memory) : iProp Σ :=
    "SIζ" ∷ ghost_var wrapperG_γζ (1/2) ζ
  ∗ "SIχ" ∷ ghost_var wrapperG_γχ (1/2) χ
  ∗ "SIθ" ∷ ghost_var wrapperG_γθ (1/2) (∅ : addr_map)
  ∗ "SIGCrem" ∷ GC_remnant ζ χ roots_m
  ∗ "SIroots" ∷ ghost_var wrapperG_γroots_set (1/2) (map dom roots_m)
  ∗ "SIbound" ∷ ghost_var wrapperG_γat_boundary (1/2) false
  ∗ "SIinit" ∷ ghost_var wrapperG_γat_init (1/2) false
  ∗ "HσCv" ∷ gen_heap_interp (roots_map_mem' memC roots_m)
  ∗ "%HmemCdisj" ∷ ⌜Forall (λ r, dom memC ## dom r) roots_m⌝.

Definition private_state_interp : wrapstateC → iProp Σ :=
  (λ ρc, C_state_interp (ζC ρc) (χC ρc) (θC ρc) (rootsC ρc))%I.

Definition wrap_state_interp (σ : Wrap.state) : iProp Σ :=
  match σ with
  | Wrap.CState ρc mem =>
      "HσC" ∷ public_state_interp mem ∗
      "SIC" ∷ private_state_interp ρc
  | Wrap.MLState ρml σ =>
      "HσML" ∷ state_interp (σ:language.language.state ML_lang) ∗
      "SIML" ∷ ML_state_interp (ζML ρml) (χML ρml) (rootsML ρml) (privmemML ρml)
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

End WrapperWP.

Ltac SI_GC_agree :=
  iDestruct (ghost_var_agree with "GCζ SIζ") as %?;
  iDestruct (ghost_var_agree with "GCχ SIχ") as %?;
  iDestruct (ghost_var_agree with "GCθ SIθ") as %?;
  iDestruct (ghost_var_agree with "GCroots SIroots") as %?;
  iDestruct (ghost_var_agree with "GCinit SIinit") as %?;
  simplify_eq.
