From Coq Require Import ssreflect.
From stdpp Require Import strings gmap.
From melocoton Require Import named_props.
From transfinite.base_logic.lib Require Import ghost_map ghost_var.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From melocoton.c_interface Require Export defs resources.
From melocoton.ml_lang Require Import lang_instantiation.
From melocoton.ml_lang Require Export lang primitive_laws.
From melocoton.interop Require Import basics_resources hybrid_ghost_heap roots.

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
  wrapperG_locsetG :> ghost_varG Σ (gsetUR loc);
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
  #[ghost_varΣ (gsetUR loc); ghost_varΣ (leibnizO addr_map);
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
    (roots_s : gset addr) (roots_m : gmap addr lval),
    "GCζ" ∷ ghost_var wrapperG_γζ (1/2) ζ
  ∗ "GCχ" ∷ ghost_var wrapperG_γχ (1/2) χ
  ∗ "GCθ" ∷ ghost_var wrapperG_γθ (1/2) θ
  ∗ "GCHGH" ∷ HGH χ (Some σMLvirt) ζ
  ∗ "GCinit" ∷ ghost_var wrapperG_γat_init (1/2) false
  ∗ "GCrootss" ∷ ghost_var wrapperG_γroots_set (1/2) roots_s
  ∗ "GCrootsm" ∷ ghost_map_auth wrapperG_γroots_map 1 roots_m
  ∗ "GCROOTS" ∷ ROOTS θ roots_m
  ∗ "%Hrootsdom" ∷ ⌜dom roots_m = roots_s⌝
  ∗ "%HGCOK" ∷ ⌜GC_correct ζ θ⌝.

Definition at_init := ghost_var wrapperG_γat_init (1/2) true.

End GCtoken.
