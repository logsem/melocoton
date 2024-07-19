From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Export defs resources.
From melocoton.ml_lang Require Import lang_instantiation.
From melocoton.ml_lang Require Export lang primitive_laws.
From melocoton.interop Require Import basics_resources hybrid_ghost_heap.

(** The [GC θ] resource.

   [GC θ] represents the collection of authoritative resources related to the ML
   runtime while running or interoperating with external C-like code. It is used
   e.g. in the points-to update laws that translate between ML and block-level
   pointsto.

   Its definition is best understood side-by-side with the wrapper state
   interpretation (in weakestpre.v), but is in its own separate file to make it
   possible to only import [GC θ] and relevant SL resources without depending on
   the wrapper WP and state interp.
 *)

Class wrapperGCtokGpre `{SI: indexT} Σ := WrapperGCtokGpre {
  wrapperG_locsetG :> ghost_varG Σ (leibnizO (list $ gset addr));
  wrapperG_addrmapG :> ghost_varG Σ (leibnizO addr_map);
  wrapperG_var_lstoreG :> ghost_varG Σ lstore;
  wrapperG_var_lloc_mapG :> ghost_varG Σ lloc_map;
  wrapperG_var_bool :> ghost_varG Σ (leibnizO bool);
}.

Class wrapperGCtokG `{SI: indexT} Σ := WrapperGCtokG {
  wrapperG_basics :> wrapperBasicsG Σ;
  wrapperG_inG :> wrapperGCtokGpre Σ;
  wrapperG_γζ : gname;
  wrapperG_γθ : gname;
  wrapperG_γχ : gname;
  wrapperG_γroots_set : gname;
  wrapperG_γat_init : gname;
}.

Definition wrapperGCtokΣ {SI: indexT} : gFunctors :=
  #[ghost_varΣ (leibnizO (list $ gset addr));
    ghost_varΣ (leibnizO addr_map);
    ghost_varΣ lstore; ghost_varΣ lloc_map; ghost_varΣ (leibnizO bool)].

Global Instance subG_wrapperGCtokGpre `{SI: indexT} Σ :
  subG wrapperGCtokΣ Σ → wrapperGCtokGpre Σ.
Proof. solve_inG. Qed.

Section GCtoken.
Context `{SI: indexT}.
Context {Σ : gFunctors}.
Context `{!heapG_ML Σ, !heapG_C Σ}.
Context `{!wrapperGCtokG Σ}.

Definition GC (θ : addr_map) : iProp Σ :=
  ∃ (ζ : lstore) (χ : lloc_map) (σMLvirt : store)
    (roots_s : list $ gset addr) (roots_fm : list roots_map) (roots_gm : roots_map)
    (roots_f : list gname) (roots_lm : gmap gname unit),
    "GCζ" ∷ ghost_var wrapperG_γζ (1/2) ζ
  ∗ "GCχ" ∷ ghost_var wrapperG_γχ (1/2) χ
  ∗ "GCθ" ∷ ghost_var wrapperG_γθ (1/2) θ
  ∗ "GCHGH" ∷ HGH χ (Some σMLvirt) ζ
  ∗ "GCinit" ∷ ghost_var wrapperG_γat_init (1/2) false
  ∗ "GCroots" ∷ ghost_var wrapperG_γroots_set (1/2) roots_s
  ∗ "GCrootslive" ∷ ghost_map_auth wrapperG_γroots_live_map 1 roots_lm
  ∗ "GCrootsf" ∷ ghost_var wrapperG_γroots_frame (1/2) roots_f
  ∗ "GCrootsg" ∷ ghost_map_auth wrapperG_γroots_global_map 1 roots_gm
  ∗ "GCrootsm" ∷ ([∗ list] f; r ∈ roots_f; roots_fm, ghost_map_auth f (1/2) r)
  ∗ "GCrootspto" ∷ ([∗ list] r ∈ (roots_fm++[roots_gm]),
                   ([∗ map] a ↦ v ∈ r, ∃ w, a ↦C w ∗ ⌜repr_lval θ v w⌝))
  ∗ "%Hrootsdom" ∷ ⌜map dom (roots_fm++[roots_gm]) = roots_s⌝
  ∗ "%Hrootslive" ∷ ⌜roots_are_live θ (roots_fm++[roots_gm])⌝
  ∗ "%Hlocalrootslive" ∷ ⌜dom roots_lm = list_to_set roots_f⌝
  ∗ "%Hlocalnodup" ∷ ⌜NoDup roots_f⌝
  ∗ "%HGCOK" ∷ ⌜GC_correct ζ θ⌝.

Definition at_init := ghost_var wrapperG_γat_init (1/2) true.

End GCtoken.
